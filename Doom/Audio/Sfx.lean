/- Sound spatialization and channel policy from pinned doom/s_sound.c.
Copyright id Software / Simon Howard. GPL-2.0-or-later. -/
import Doom.Audio.Pcm
import Doom.Audio.Tables
import Doom.Angles
import Doom.Random
namespace Doom.Audio.Sfx

inductive Origin where
  | actor (id : Nat) | sector (id : Nat) | missile (id : Nat)
  deriving BEq, Repr, Inhabited
structure Position where
  x : Fixed
  y : Fixed
  deriving Inhabited, Repr
structure Listener extends Position where
  angle : Angle
  deriving Inhabited
structure Params where
  volume : Nat
  separation : Nat := 128
  deriving BEq, Repr, Inhabited

/-- Preserve the original binary-angle off-by-one and close/clipping distances.
DOOM map 8's nonzero distant-volume exception is supported separately. -/
def adjust (listener : Listener) (source : Position) (volume : Nat) (map8 : Bool := false) : Except String (Option Params) := do
  let dx := (listener.x-source.x).raw; let dy := (listener.y-source.y).raw
  if dx == -2147483648 || dy == -2147483648 then throw "sound: undefined reference absolute value"
  let ax := dx.toInt.natAbs; let ay := dy.toInt.natAbs
  let distance := (Int32.ofNat (ax+ay-min ax ay/2)).toInt
  if !map8 && distance > 1200*65536 then return none
  let angle := (Angle.fromVector (source.x-listener.x) (source.y-listener.y)).raw
  let angle := if angle > listener.angle.raw then angle-listener.angle.raw else angle+(0xffffffff-listener.angle.raw)
  let swing := Fixed.ofInt 96 * (⟨angle⟩ : Angle).fineSine
  let sep := 128-(swing.raw >>> 16).toInt
  let vol := if distance < 200*65536 then Int.ofNat volume
    else if map8 then 15+((Int.ofNat volume-15)*((1200*65536-min distance (1200*65536))/65536)).tdiv 1000
    else (Int.ofNat volume*((1200*65536-distance)/65536)).tdiv 1000
  return if vol > 0 then some ⟨vol.toNat,sep.toNat⟩ else none

structure Channel where
  name : String
  origin : Option Origin
  position : Position
  sample : Sample
  priority : Nat
  pitch : Nat
  params : Params
  phase : Nat := 0
  deriving Inhabited
structure State where
  bank : Array (String × Sample)
  channels : Array (Option Channel) := Array.replicate 8 none
  volume : Nat := 64
  map8 : Bool := false
  deriving Inhabited
structure Event where
  name : String
  origin : Option Origin
  position : Position
  deriving Repr

/-- Last WAD definition wins; only digital DS lumps belong to this backend. -/
def load (lumps : Array Lump) : Except String (Array (String × Sample)) := do
  let mut result := #[]
  for i in [:lumps.size] do
    let lump := lumps[i]!
    if !lump.name.startsWith "DS" || findLump lumps lump.name != some i then continue
    let sample ← (Sample.parse lump.bytes).mapError fun e => s!"{lump.name}: {e}"
    result := result.push ((lump.name.drop 2).toString.toLower,sample)
  return result

/-- Original S_StopSound stops the first channel with this origin. -/
def State.stop (s : State) (origin : Option Origin) : State :=
  match s.channels.findIdx? (fun c => c.any (·.origin == origin)) with
  | none => s
  | some i => { s with channels := s.channels.set! i none }

/-- Logical sound setup precedes the output backend, including with -nosound.
Audibility gates the pitch RNG draw, but allocating an output channel does not. -/
def State.prepare (s : State) (listener : Listener) (e : Event) (rng : DoomRandom)
    : Except String (Option (Params × Nat × DoomRandom)) := do
  if !(Tables.sfx.any (·.1 == e.name)) then throw s!"sound: unknown effect {e.name}"
  let mut params : Params := ⟨s.volume,128⟩
  if e.origin.isSome && e.origin != some (.actor 0) then
    let some p ← adjust listener e.position s.volume s.map8 | return none
    params := p
    if e.position.x == listener.x && e.position.y == listener.y then params := { params with separation := 128 }
  let mut pitch := 128
  let mut rng := rng
  if e.name != "itemup" && e.name != "tink" then
    let (random,next) := rng.nextMisc
    rng := next
    pitch := if #["sawup","sawidl","sawful","sawhit"].contains e.name then 136-(random &&& 15) else 144-(random &&& 31)
  return some (params,pitch,rng)

def State.start (s : State) (listener : Listener) (e : Event) (rng : DoomRandom) : Except String (State × DoomRandom) := do
  let some (params,pitch,rng) ← s.prepare listener e rng | return (s,rng)
  let some info := Tables.sfx.find? (·.1 == e.name) | throw s!"sound: unknown effect {e.name}"
  let mut channels := s.channels
  if let some i := channels.findIdx? (fun c => c.any (·.origin == e.origin)) then channels := channels.set! i none
  let index := channels.findIdx? fun c => c.isNone || (e.origin.isSome && c.any (·.origin == e.origin))
  let index := index.orElse fun _ => channels.findIdx? fun c => c.any (·.priority ≥ info.2)
  let some index := index | return ({ s with channels },rng)
  let some sample := s.bank.find? (·.1 == e.name) | throw s!"sound: missing DS{e.name.toUpper}"
  let c : Channel := ⟨e.name,e.origin,e.position,sample.2,info.2,pitch,params,0⟩
  return ({ s with channels := channels.set! index (some c) },rng)

/-- Moving emitters follow their actor/sector identity. Runtime removal calls
State.stop, matching P_RemoveMobj; no native pointer enters the mixer. -/
def State.update (s : State) (listener : Listener) (position : Origin → Option Position) : Except String State := do
  let mut s := s
  for i in [:s.channels.size] do
    let some c := s.channels[i]! | continue
    if c.origin.isNone || c.origin == some (.actor 0) then continue
    let pos := c.origin.bind position |>.getD c.position
    let p ← adjust listener pos s.volume s.map8
    s := { s with channels := s.channels.set! i (p.map fun p => { c with position := pos, params := p }) }
  return s

/-- Deterministic signed PCM mixer. Rational sample cursors preserve fractional
pitch across blocks; interpolation is an output-backend choice, not DOS DAC parity.
The pitch-duration ratio is Chocolate Doom's measured DMX approximation. -/
def State.sample (s : State) : (Int × Int) × State := Id.run do
  let mut s := s
  let mut left := 0; let mut right := 0
  for i in [:s.channels.size] do
    let some c := s.channels[i]! | continue
    let denominator := sampleRate*(256-c.pitch)
    let index := c.phase/denominator
    if index ≥ c.sample.data.size then
      s := { s with channels := s.channels.set! i none }
      continue
    let value := (Int.ofNat c.sample.data[index]!.toNat-128)*256
    let next := (Int.ofNat c.sample.data[min (index+1) (c.sample.data.size-1)]!.toNat-128)*256
    let value := value + ((next-value)*Int.ofNat (c.phase%denominator)).tdiv denominator
    let l := min 255 ((254-c.params.separation)*c.params.volume/127)
    let r := min 255 (c.params.separation*c.params.volume/127)
    left := left+(value*Int.ofNat l).tdiv 255
    right := right+(value*Int.ofNat r).tdiv 255
    let phase := c.phase+c.sample.rate*128
    let next := if phase/denominator ≥ c.sample.data.size then none else some { c with phase }
    s := { s with channels := s.channels.set! i next }
  return ((left,right),s)

end Doom.Audio.Sfx

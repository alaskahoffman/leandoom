/- DOOM 1.9 nine-voice GENMIDI driver. Port of Chocolate Doom i_oplmusic.c.
Copyright id Software / Simon Howard. GPL-2.0-or-later. -/
import Doom.Audio.Opl
import Doom.Audio.Mus
namespace Doom.Audio.Music
open Binary Tables

structure Operator where
  tremolo : Nat
  attack : Nat
  sustain : Nat
  wave : Nat
  scale : Nat
  level : Nat
  deriving Inhabited
structure Patch where
  modulator : Operator
  carrier : Operator
  feedback : Nat
  offset : Int
  deriving Inhabited
structure Instrument where
  flags : Nat
  tuning : Nat
  note : Nat
  voices : Array Patch
  deriving Inhabited

def instruments (data : ByteArray) : Parse (Array Instrument) := do
  require (data.extract 0 8 == "#OPL_II#".toUTF8) "GENMIDI: invalid signature"
  checkRange data 8 (175*36)
  let op := fun o => (⟨data[o]!.toNat,data[o+1]!.toNat,data[o+2]!.toNat,
    data[o+3]!.toNat,data[o+4]!.toNat,data[o+5]!.toNat⟩ : Operator)
  let mut bank := #[]
  for i in [:175] do
    let pos := 8+i*36
    let mut voices := #[]
    for v in [:2] do
      let p := pos+4+v*16
      voices := voices.push ⟨op p,op (p+7),data[p+6]!.toNat,← i16 data (p+14)⟩
    bank := bank.push ⟨← u16 data pos,data[pos+2]!.toNat,data[pos+3]!.toNat,voices⟩
  return bank

structure Channel where
  instrument : Nat := 0
  volume : Nat := 64
  bend : Int := 0
  deriving Inhabited
structure Voice where
  instrument : Option Nat := none
  patch : Nat := 0
  channel : Option Nat := none
  key : Nat := 0
  note : Nat := 0
  frequency : Nat := 0
  volume : Nat := 0
  carrierLevel : Nat := 0
  modulatorLevel : Nat := 0
  deriving Inhabited
structure Driver where
  bank : Array Instrument
  chip : Opl.Chip := {}
  channels : Array Channel := Array.replicate 16 {}
  voices : Array Voice := Array.replicate 9 {}
  free : Array Nat := #[0,1,2,3,4,5,6,7,8]
  allocated : Array Nat := #[]
  volume : Nat := 64
  writes : Array (Nat × Nat) := #[]
  deriving Inhabited

abbrev M := StateT Driver (Except String)
private def write (reg value : Nat) : M Unit := do
  let s ← get
  let chip ← s.chip.write reg value
  set { s with chip, writes := s.writes.push (reg,value &&& 255) }
private def voice (id : Nat) : M Voice := return (← get).voices[id]!
private def change (id : Nat) (f : Voice → Voice) : M Unit := modify fun s => { s with voices := s.voices.set! id (f s.voices[id]!) }
private def operator1 (id : Nat) : Nat := #[0,1,2,8,9,10,16,17,18][id]!
private def release (index : Nat) : M Unit := do
  let s ← get
  let id := s.allocated[index]!
  write (0xb0+id) (s.voices[id]!.frequency >>> 8)
  change id fun v => { v with channel := none, note := 0 }
  modify fun s => { s with allocated := s.allocated.extract 0 index ++ s.allocated.extract (index+1) s.allocated.size, free := s.free.push id }

private def loadOperator (reg : Nat) (data : Operator) (quiet : Bool) : M Nat := do
  let level := data.scale ||| (if quiet then 63 else data.level)
  write (0x40+reg) level
  write (0x20+reg) data.tremolo
  write (0x60+reg) data.attack
  write (0x80+reg) data.sustain
  write (0xe0+reg) data.wave
  return level

private def setInstrument (id instrument patch : Nat) : M Unit := do
  let v ← voice id
  if v.instrument == some instrument && v.patch == patch then return
  let data := (← get).bank[instrument]!.voices[patch]!
  change id fun v => { v with instrument := some instrument, patch }
  let carrierLevel ← loadOperator (operator1 id+3) data.carrier true
  let modulatorLevel ← loadOperator (operator1 id) data.modulator (data.feedback &&& 1 != 0)
  change id fun v => { v with carrierLevel,modulatorLevel }
  write (0xc0+id) (data.feedback ||| 0x30)

private def setVolume (id volume : Nat) : M Unit := do
  change id fun v => { v with volume }
  let s ← get; let v := s.voices[id]!
  let data := s.bank[v.instrument.getD 0]!.voices[v.patch]!
  let channelVolume := s.channels[v.channel.getD 0]!.volume
  let full := (volume_mapping_table[volume]! * (2*(volume_mapping_table[channelVolume]!+1))) >>> 9
  let carrier := 63-full
  if carrier == v.carrierLevel &&& 63 then return
  let carrier := carrier ||| (v.carrierLevel &&& 192)
  change id fun v => { v with carrierLevel := carrier }
  write (0x40+operator1 id+3) carrier
  if data.feedback &&& 1 != 0 && data.modulator.level != 63 then
    let level := max data.modulator.level (carrier &&& 63) ||| (v.modulatorLevel &&& 192)
    if level != v.modulatorLevel then
      change id fun v => { v with modulatorLevel := level }
      write (0x40+operator1 id) (level ||| (data.modulator.scale &&& 192))

private def frequency (s : Driver) (v : Voice) : Nat := Id.run do
  let instrument := s.bank[v.instrument.getD 0]!
  let patch := instrument.voices[v.patch]!
  let mut note := Int.ofNat v.note + (if instrument.flags &&& 1 == 0 then patch.offset else 0)
  -- Equivalent to the original +/-12 loops, including out-of-range offsets.
  if note < 0 then note := note%12
  if note > 95 then note := 84+(note-84)%12
  let index := max 0 (64+32*note+s.channels[v.channel.getD 0]!.bend+
    (if v.patch != 0 then Int.ofNat (instrument.tuning/2)-64 else 0))
  let index := index.toNat
  if index < 284 then return frequency_curve[index]!
  return frequency_curve[(index-284)%384+284]! ||| (min 7 ((index-284)/384) <<< 10)

private def updateFrequency (id : Nat) : M Unit := do
  let s ← get; let v := s.voices[id]!
  let value := frequency s v
  if v.frequency != value then
    write (0xa0+id) (value &&& 255)
    write (0xb0+id) ((value >>> 8) ||| 32)
    change id fun v => { v with frequency := value }

private def keyOn (channel instrument patch note key volume : Nat) : M Unit := do
  let s ← get
  let some id := s.free[0]? | return
  let instr := s.bank[instrument]!
  set { s with free := s.free.extract 1 s.free.size, allocated := s.allocated.push id }
  change id fun v => { v with channel := some channel, key, note := if instr.flags &&& 1 != 0 then instr.note else note }
  setInstrument id instrument patch
  setVolume id volume
  change id fun v => { v with frequency := 0 }
  updateFrequency id

private def keyOff (channel : Nat) (key : Option Nat) : M Unit := do
  let mut i := 0
  for _ in [:9] do
    let s ← get
    if i ≥ s.allocated.size then break
    let v := s.voices[s.allocated[i]!]!
    if v.channel == some channel && (key.isNone || key == some v.key) then release i
    else i := i+1

/-- The single MUS track converted by mus2mid; nine-voice DOOM 1.9 allocation.
Unused controller messages are ignored just as by the original OPL driver. -/
def event (e : MidiEvent) : M Unit := do
  let midiChannel := e.status &&& 15
  let channel := if midiChannel == 9 then 15 else if midiChannel == 15 then 9 else midiChannel
  match e.status &&& 0xf0 with
  | 0x80 => keyOff channel (some e.a)
  | 0x90 =>
    if e.b == 0 then keyOff channel (some e.a); return
    if midiChannel == 9 && (e.a < 35 || e.a > 81) then return
    let s ← get
    let instrument := if midiChannel == 9 then 128+e.a-35 else s.channels[channel]!.instrument
    if s.free.isEmpty then
      let mut selected := 0
      for i in [:s.allocated.size] do
        let a := s.voices[s.allocated[i]!]!; let b := s.voices[s.allocated[selected]!]!
        if a.patch != 0 || a.channel.getD 0 ≥ b.channel.getD 0 then selected := i
      release selected
    let note := if midiChannel == 9 then 60 else e.a
    keyOn channel instrument 0 note e.a e.b
    if (← get).bank[instrument]!.flags &&& 4 != 0 then keyOn channel instrument 1 note e.a e.b
  | 0xc0 => modify fun s => { s with channels := s.channels.set! channel { s.channels[channel]! with instrument := e.a } }
  | 0xb0 =>
    if e.a == 123 then keyOff channel none
    else if e.a == 7 then
      modify fun s => { s with channels := s.channels.set! channel { s.channels[channel]! with volume := min e.b s.volume } }
      for id in [:9] do
        let v ← voice id
        if v.channel == some channel then setVolume id v.volume
  | 0xe0 =>
    modify fun s => { s with channels := s.channels.set! channel { s.channels[channel]! with bend := Int.ofNat e.b-64 } }
    let mut updated := #[]; let mut others := #[]
    for id in (← get).allocated do
      if (← voice id).channel == some channel then
        updateFrequency id
        updated := updated.push id
      else others := others.push id
    modify fun s => { s with allocated := others ++ updated }
  | _ => pure ()

def Driver.handle (s : Driver) (e : MidiEvent) : Except String Driver := do
  return (← (event e).run s).2

structure Player where
  driver : Driver
  score : Score
  position : Nat := 0
  cursor : Nat := 0
  loops : Nat := 0
  deriving Inhabited

def Player.start (bank : Array Instrument) (score : Score) (volume : Nat := 64) : Player :=
  { driver := { bank, volume := min 127 volume, channels := Array.replicate 16 { volume := min 100 (min 127 volume) } }, score }

/-- Render MUS at its 140-Hz clock. State survives arbitrary output block sizes;
looping resets channels while preserving the chip's release tails and allocator. -/
def Player.render (s : Player) (frames : Nat) : Except String (Array (Int × Int) × Player) := do
  let mut s := { s with driver := { s.driver with writes := #[] } }
  let mut samples := #[]
  for _ in [:frames] do
    for pass in [:2] do
      for _ in [:s.score.events.size+1] do
        let some e := s.score.events[s.cursor]? | break
        if e.tick*315 > s.position then break
        s := { s with driver := ← s.driver.handle e, cursor := s.cursor+1 }
      if pass == 0 && s.position == s.score.duration*315 then
        s := { s with
          position := 0, cursor := 0, loops := s.loops+1,
          driver := { s.driver with channels := Array.replicate 16 { volume := min 100 s.driver.volume } } }
      else break
    let (pcm,chip) := s.driver.chip.sample
    samples := samples.push pcm
    s := { s with position := s.position+1, driver := { s.driver with chip } }
  return (samples,s)

end Doom.Audio.Music

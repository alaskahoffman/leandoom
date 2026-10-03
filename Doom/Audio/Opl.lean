/- Two-operator, nine-voice OPL profile used by DOOM 1.9 AdLib music.
Port of Nuked OPL3 1.8 (Alexey Khokholov), pinned in Chocolate Doom 3.1.1.
GPL-2.0-or-later. Rhythm mode and the OPL3 register bank are rejected.
DOOM plays percussion using melodic GENMIDI voices, not hardware rhythm mode. -/
import Doom.Audio.Tables
namespace Doom.Audio.Opl
open Tables

structure Slot where
  out : Int := 0
  previous : Int := 0
  envelope : Nat := 511
  stage : Nat := 3 -- attack, decay, sustain, release
  phase : UInt32 := 0
  key : Bool := false
  trem : Bool := false
  vib : Bool := false
  sustained : Bool := false
  ksr : Bool := false
  multiple : Nat := 0
  ksl : Nat := 0
  level : Nat := 0
  attack : Nat := 0
  decay : Nat := 0
  sustain : Nat := 0
  release : Nat := 0
  wave : Nat := 0
  deriving Inhabited

structure Channel where
  frequency : Nat := 0
  block : Nat := 0
  feedback : Nat := 0
  additive : Bool := false
  deriving Inhabited

structure Chip where
  slots : Array Slot := Array.replicate 18 {}
  channels : Array Channel := Array.replicate 9 {}
  timer : Nat := 0
  egTimer : Nat := 0
  egRemainder : Bool := false
  egState : Nat := 0
  egAdd : Nat := 0
  nts : Nat := 0
  vibrato : Nat := 0
  vibShift : Nat := 1
  tremolo : Nat := 0
  tremoloPos : Nat := 0
  tremoloShift : Nat := 4
  right : Int := 0
  sampleCount : Nat := 0
  oldLeft : Int := 0
  oldRight : Int := 0
  leftSample : Int := 0
  rightSample : Int := 0
  deriving Inhabited

private def wrap16 (n : Int) : Int := (Int16.ofInt n).toInt
private def clip (n : Int) : Int := max (-32768) (min 32767 n)
private def shift (n : Int) (k : Nat) : Int := n / (2^k : Nat)

private def waveform (wave phase envelope : Nat) : Int := Id.run do
  let phase := phase &&& 1023
  let mirrored := if phase &&& 256 != 0 then (phase &&& 255) ^^^ 255 else phase &&& 255
  let attenuation := if wave == 1 && phase &&& 512 != 0 then 4096
    else if wave == 3 && phase &&& 256 != 0 then 4096
    else logsinrom[if wave == 3 then phase &&& 255 else mirrored]!
  let level := min 8191 (attenuation+envelope*8)
  let value := (exprom[level &&& 255]! * 2) >>> (level >>> 8)
  return if wave == 0 && phase &&& 512 != 0 then -(Int.ofNat value)-1 else Int.ofNat value

private def stepSlot (chip : Chip) (id : Nat) : Chip := Id.run do
  let ci := (id/6)*3+id%3
  let channel := chip.channels[ci]!
  let mut slot := chip.slots[id]!
  let fb := if channel.feedback == 0 then 0 else shift (slot.previous+slot.out) (9-channel.feedback)
  slot := { slot with previous := slot.out }
  let ksl := (max (0 : Int) (Int.ofNat (kslrom[channel.frequency >>> 6]!*4) - Int.ofNat ((8-channel.block)*32))).toNat
  let envOut := slot.envelope+slot.level*4+(ksl >>> kslshift[slot.ksl]!)+(if slot.trem then chip.tremolo else 0)
  let reset := slot.key && slot.stage == 3
  let rate := if reset || slot.stage == 0 then slot.attack else if slot.stage == 1 then slot.decay
    else if slot.stage == 3 || !slot.sustained then slot.release else 0
  let ksv := (channel.block*2) ||| ((channel.frequency >>> (9-chip.nts)) &&& 1)
  let ks := ksv >>> (if slot.ksr then 0 else 2)
  let fullRate := ks+rate*4
  let hi := min 15 (fullRate >>> 2); let lo := fullRate &&& 3
  let mut amount := 0
  if rate != 0 then
    if hi < 12 then
      if chip.egState != 0 then
        amount := match hi+chip.egAdd with
          | 12 => 1 | 13 => (lo >>> 1) &&& 1 | 14 => lo &&& 1 | _ => 0
    else
      amount := (hi &&& 3)+eg_incstep[lo*4+(chip.timer &&& 3)]!
      if amount &&& 4 != 0 then amount := 3
      if amount == 0 then amount := chip.egState
  let mut rout := if reset && hi == 15 then 0 else slot.envelope
  let off := slot.envelope &&& 504 == 504
  if slot.stage != 0 && !reset && off then rout := 511
  let mut inc : Int := 0
  if slot.stage == 0 then
    if slot.envelope == 0 then slot := { slot with stage := 1 }
    else if slot.key && amount > 0 && hi != 15 then
      inc := shift ((-(Int.ofNat slot.envelope)-1)*(2^amount : Nat)) 4
  else if slot.stage == 1 then
    if slot.envelope >>> 4 == slot.sustain then slot := { slot with stage := 2 }
    else if !off && !reset && amount > 0 then inc := Int.ofNat (2^(amount-1))
  else if !off && !reset && amount > 0 then inc := Int.ofNat (2^(amount-1))
  slot := { slot with envelope := ((Int.ofNat rout+inc)%512).toNat }
  if reset then slot := { slot with stage := 0 }
  if !slot.key then slot := { slot with stage := 3 }
  let mut frequency := Int.ofNat channel.frequency
  if slot.vib then
    let mut range := (channel.frequency >>> 7) &&& 7
    if chip.vibrato &&& 3 == 0 then range := 0
    else if chip.vibrato &&& 1 != 0 then range := range >>> 1
    range := range >>> chip.vibShift
    frequency := frequency + (if chip.vibrato &&& 4 != 0 then -(Int.ofNat range) else Int.ofNat range)
  let frequencyNat := (UInt16.ofInt frequency).toNat
  let base := (frequencyNat <<< channel.block) >>> 1
  let phase := (slot.phase >>> 9).toUInt16.toNat
  let next := (if reset then 0 else slot.phase) + UInt32.ofNat ((base*mt[slot.multiple]!) >>> 1)
  let modulation := if id%6 < 3 then fb else if channel.additive then 0 else chip.slots[id-3]!.out
  let phase := (UInt16.ofInt (Int.ofNat phase+modulation)).toNat
  slot := { slot with phase := next, out := waveform slot.wave phase envOut }
  return { chip with slots := chip.slots.set! id slot }

private def sum (chip : Chip) : Int := Id.run do
  let mut total := 0
  for c in [:9] do
    let id := ch_slot[c]!
    let value := chip.slots[id+3]!.out + (if chip.channels[c]!.additive then chip.slots[id]!.out else 0)
    total := total + wrap16 value
  return total

/-- Preserve Nuked's operator pipeline order and one-sample right-channel delay.
Inactive second-bank operators contribute zero in this restricted profile. -/
def Chip.generate (chip : Chip) : (Int × Int) × Chip := Id.run do
  let mut chip := chip
  let right := clip chip.right
  for id in [:15] do chip := stepSlot chip id
  let left := clip (sum chip)
  for id in [15:18] do chip := stepSlot chip id
  chip := { chip with right := sum chip }
  if chip.timer &&& 63 == 63 then chip := { chip with tremoloPos := (chip.tremoloPos+1)%210 }
  chip := { chip with tremolo := (if chip.tremoloPos < 105 then chip.tremoloPos else 210-chip.tremoloPos) >>> chip.tremoloShift }
  if chip.timer &&& 1023 == 1023 then chip := { chip with vibrato := (chip.vibrato+1) &&& 7 }
  chip := { chip with timer := (chip.timer+1)%65536, egAdd := 0 }
  if chip.egTimer != 0 then
    let mut zeros := 0
    for _ in [:36] do
      if (chip.egTimer >>> zeros) &&& 1 != 0 then break
      zeros := zeros+1
    chip := { chip with egAdd := if zeros > 12 then 0 else zeros+1 }
  if chip.egRemainder || chip.egState != 0 then
    if chip.egTimer == 0xfffffffff then chip := { chip with egTimer := 0, egRemainder := true }
    else chip := { chip with egTimer := chip.egTimer+1, egRemainder := false }
  chip := { chip with egState := chip.egState ^^^ 1 }
  return ((left,right),chip)

/-- Original fixed-point linear output resampler, 44,100 Hz. -/
def Chip.sample (chip : Chip) : (Int × Int) × Chip := Id.run do
  let ratio := 44100*1024/49716
  let mut chip := chip
  for _ in [:3] do
    if chip.sampleCount < ratio then break
    chip := { chip with oldLeft := chip.leftSample, oldRight := chip.rightSample }
    let ((l,r),next) := chip.generate
    chip := { next with leftSample := l, rightSample := r, sampleCount := next.sampleCount-ratio }
  let l := (chip.oldLeft*Int.ofNat (ratio-chip.sampleCount)+chip.leftSample*Int.ofNat chip.sampleCount).tdiv ratio
  let r := (chip.oldRight*Int.ofNat (ratio-chip.sampleCount)+chip.rightSample*Int.ofNat chip.sampleCount).tdiv ratio
  return ((wrap16 l,wrap16 r),{ chip with sampleCount := chip.sampleCount+1024 })

def Chip.write (chip : Chip) (reg value : Nat) : Except String Chip := do
  if reg > 255 then throw "OPL: OPL3 bank is outside the nine-voice profile"
  let value := value &&& 255
  if reg == 8 then return { chip with nts := (value >>> 6) &&& 1 }
  if reg == 0xbd then
    if value &&& 63 != 0 then throw "OPL: hardware rhythm mode is outside the DOOM profile"
    return { chip with tremoloShift := ((value >>> 7) ^^^ 1)*2+2, vibShift := ((value >>> 6) &&& 1) ^^^ 1 }
  let family := reg &&& 0xe0
  if #[0x20,0x40,0x60,0x80,0xe0].contains family then
    let id := ad_slot[reg &&& 31]!
    if id < 0 then return chip
    let id := id.toNat
    let slot := chip.slots[id]!
    let slot := match family with
      | 0x20 => { slot with
          trem := value &&& 128 != 0, vib := value &&& 64 != 0,
          sustained := value &&& 32 != 0, ksr := value &&& 16 != 0, multiple := value &&& 15 }
      | 0x40 => { slot with ksl := value >>> 6, level := value &&& 63 }
      | 0x60 => { slot with attack := value >>> 4, decay := value &&& 15 }
      | 0x80 => { slot with sustain := if value >>> 4 == 15 then 31 else value >>> 4, release := value &&& 15 }
      | _ => { slot with wave := value &&& 3 }
    return { chip with slots := chip.slots.set! id slot }
  let c := reg &&& 15
  if c ≥ 9 then return chip
  let ch := chip.channels[c]!
  match reg &&& 0xf0 with
  | 0xa0 => return { chip with channels := chip.channels.set! c { ch with frequency := (ch.frequency &&& 0x300) ||| value } }
  | 0xb0 =>
    let ch := { ch with frequency := (ch.frequency &&& 255) ||| ((value &&& 3) <<< 8), block := (value >>> 2) &&& 7 }
    let id := ch_slot[c]!
    let slots := (chip.slots.set! id { chip.slots[id]! with key := value &&& 32 != 0 }).set! (id+3) { chip.slots[id+3]! with key := value &&& 32 != 0 }
    return { chip with channels := chip.channels.set! c ch, slots }
  | 0xc0 => return { chip with channels := chip.channels.set! c { ch with feedback := (value >>> 1) &&& 7, additive := value &&& 1 != 0 } }
  | _ => return chip

end Doom.Audio.Opl

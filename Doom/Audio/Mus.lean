/- MUS decoding follows the pinned Chocolate Doom mus2mid.c event mapping.
Copyright 1993-1996 id Software, 2005-2014 Simon Howard, 2006 Ben Ryves.
Adapted to Lean with explicit parser bounds on 2026-10-03.
GPL-2.0-or-later. Bounds and malformed-input rejection are explicit. -/
import Doom.Binary
namespace Doom.Audio
open Binary

structure MidiEvent where
  tick : Nat
  status : Nat
  a : Nat
  b : Nat := 0
  deriving BEq, Repr, Inhabited

structure Score where
  events : Array MidiEvent
  duration : Nat
  deriving Inhabited

private def byte (bytes : ByteArray) (offset : Nat) : Parse Nat := do
  checkRange bytes offset 1
  return bytes[offset]!.toNat

/-- MUS clocks at 140 Hz; a 44,100-Hz output has exactly 315 samples per tick.
Channel allocation and the initial all-notes-off follow mus2mid.c. -/
def Score.parse (bytes : ByteArray) : Parse Score := do
  checkRange bytes 0 16
  require (bytes.extract 0 4 == ByteArray.mk #[77,85,83,26]) "MUS: invalid signature"
  let length ← u16 bytes 4; let start ← u16 bytes 6
  let channels ← u16 bytes 8; let instruments ← u16 bytes 12
  require (channels ≤ 15 && start ≥ 16+2*instruments) "MUS: invalid header"
  checkRange bytes 16 (2*instruments)
  checkRange bytes start length
  let bytes := bytes.extract start (start+length)
  let mut pos := 0; let mut time := 0
  let mut channelMap : Array (Option Nat) := Array.replicate 16 none
  let mut velocities := Array.replicate 16 127
  let mut allocated := 0
  let mut events := #[]
  for _ in [:bytes.size+1] do
    let descriptor ← byte bytes pos; pos := pos+1
    let musChannel := descriptor &&& 15
    let channel ← if musChannel == 15 then pure 9 else do
      if let some channel := channelMap[musChannel]! then pure channel else do
        let channel := if allocated ≥ 9 then allocated+1 else allocated
        require (channel < 16) "MUS: too many channels"
        allocated := allocated+1
        channelMap := channelMap.set! musChannel (some channel)
        events := events.push ⟨time,0xb0+channel,123,0⟩
        pure channel
    let kind := (descriptor >>> 4) &&& 7
    match kind with
    | 0 =>
      let key ← byte bytes pos; pos := pos+1
      events := events.push ⟨time,0x80+channel,key &&& 127,0⟩
    | 1 =>
      let key ← byte bytes pos; pos := pos+1
      if key &&& 128 != 0 then
        let velocity ← byte bytes pos; pos := pos+1
        velocities := velocities.set! channel (velocity &&& 127)
      events := events.push ⟨time,0x90+channel,key &&& 127,velocities[channel]!⟩
    | 2 =>
      let pitch ← byte bytes pos; pos := pos+1
      events := events.push ⟨time,0xe0+channel,(pitch*64) &&& 127,(pitch*64) >>> 7⟩
    | 3 =>
      let control ← byte bytes pos; pos := pos+1
      require (control ≥ 10 && control ≤ 14) "MUS: invalid system event"
      events := events.push ⟨time,0xb0+channel,#[120,123,126,127,121][control-10]!,0⟩
    | 4 =>
      let control ← byte bytes pos; let value ← byte bytes (pos+1); pos := pos+2
      require (control ≤ 9) "MUS: invalid controller"
      if control == 0 then events := events.push ⟨time,0xc0+channel,value &&& 127,0⟩
      else events := events.push ⟨time,0xb0+channel,#[0,32,1,7,10,11,91,93,64,67][control]!,min value 127⟩
    | 6 =>
      require (time > 0) "MUS: zero-duration score"
      return ⟨events,time⟩
    | _ => throw "MUS: unsupported event type"
    if descriptor &&& 128 != 0 then
      let mut delay := 0; let mut done := false
      for _ in [:5] do
        let value ← byte bytes pos; pos := pos+1
        delay := delay*128+(value &&& 127)
        require (delay ≤ 0x0fffffff) "MUS: delay overflow"
        if value &&& 128 == 0 then done := true; break
      require done "MUS: unterminated delay"
      time := time+delay
      require (time ≤ 140*3600) "MUS: score exceeds one hour"
  throw "MUS: missing score end"

end Doom.Audio

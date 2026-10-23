import Doom.Proofs.OriginalKillEntry
open Doom.Verification X86 X86Memory X86Control X86Routine
#eval Id.run do
  if X86Routine.decodeAt [0x81,0xea,0x78,0xae,2,0] 0 != some (.addImmediate 2 (-0x2ae78),6) then return false
  if (X86Routine.decodeAt [0x81,0xea,0x78,0xae,2] 0).isSome then return false
  if (X86Routine.decodeAt [0x80,0xe1] 0).isSome then return false
  for dst in [:8] do
    let r : Reg := ⟨dst % 8,Nat.mod_lt _ (by decide)⟩
    if X86Routine.decodeAt [0x80,UInt8.ofNat (0xe0+dst),0xfd] 0 != some (.andByteImmediate r 0xfd,3) then return false
    for n in [:256] do
      let value : Word := (if dst < 4 then 0xa5a5a500 else 0xa5a500a5) ||| (BitVec.ofNat 32 n <<< (if dst < 4 then 0 else 8))
      let s : X86Control.State := ⟨⟨fun _ => value,fun _ => 0⟩,none,0⟩
      let expected := readByte s.core.regs r &&& (0xfd#8)
      let some t := X86Routine.execute (.andByteImmediate r 0xfd) s | return false
      for j in [:8] do
        if t.core.regs ⟨j % 8,Nat.mod_lt _ (by decide)⟩ != (putByte s.core r expected).regs ⟨j % 8,Nat.mod_lt _ (by decide)⟩ then return false
      if t.core.memory 0 != 0 then return false
      if t.flags != some {zero := expected==0,sign := expected.msb,overflow := false,carry := some false} then return false
  for value in ([0,1,0x2ae78,0x80000000,0xffffffff] : List Word) do
    let s : X86Control.State := ⟨⟨fun _ => value,fun _ => 0⟩,none,0⟩
    let some t := X86Routine.execute (.addImmediate 2 (-0x2ae78)) s | return false
    if t.core.regs 2 != value-(0x2ae78#32) || t.core.regs 3 != value then return false
    if t.flags.isSome then return false
  return true

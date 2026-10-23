import Doom.Proofs.OriginalKillEntry
open Doom.Verification X86 X86Memory X86Control X86Routine

-- Independently exercise the added byte-AND and word-OR decoder cases.
-- Unsupported ADC encodings still fail closed.
#eval Id.run do
  if X86Routine.decodeAt [0x80,0x63,0x69,0xfd] 0 != some (.andMemoryByte ⟨some 3,none,0,105⟩ 0xfd,4) then return false
  if X86Routine.decodeAt [0x81,0xcf,0,4,0x10,0] 0 != some (.orRegister 7 0x100400,6) then return false
  if X86Routine.decodeAt [0x80,0xe1,0xfd] 0 != some (.andByteImmediate 1 0xfd,3) then return false
  if (X86Routine.decodeAt [0x81,0xd7,0,4,0x10,0] 0).isSome then return false
  if (X86Routine.decodeAt [0x80,0x63,0x69] 0).isSome then return false
  if (X86Routine.decodeAt [0x81,0xcf,0,4,0x10] 0).isSome then return false
  for addr in ([0,1,0xffffffff] : List Word) do
    for n in [:256] do
      let s : X86Control.State := ⟨⟨fun _ => addr,fun _ => BitVec.ofNat 8 n⟩,none,0⟩
      let some t := X86Routine.execute (.andMemoryByte ⟨some 3,none,0,0⟩ 0xfd) s | return false
      let value := BitVec.ofNat 8 n &&& (0xfd#8)
      if t.core.memory addr != value || t.core.memory (addr+1) != BitVec.ofNat 8 n then return false
      if t.core.memory (addr-1) != BitVec.ofNat 8 n then return false
      if t.flags != some {zero := value==0,sign := value.msb,overflow := false,carry := some false} then return false
  for value in ([0,1,0x80000000,0xffffffff,0x100400] : List Word) do
    let s : X86Control.State := ⟨⟨fun _ => value,fun _ => 0⟩,none,0⟩
    let some t := X86Routine.execute (.orRegister 7 0x100400) s | return false
    let expected := value ||| (0x100400#32)
    if t.core.regs 7 != expected || t.core.regs 6 != value then return false
    if t.flags != some {zero := expected==0,sign := expected.msb,overflow := false,carry := some false} then return false
  return true

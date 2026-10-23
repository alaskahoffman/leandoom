import Doom.Proofs.OriginalPainHandoff
open Doom.Verification X86 X86Memory X86Control

-- All AL..BH encodings and byte values; upper/lower adjacent bits are preserved.
#eval Id.run do
  for r in [:8] do
    for value in [:256] do
      for mask in [0,1,64,255] do
        let rs : Registers := fun k => if k.val == r%4 then
          if r<4 then 0xa5c3d200 ||| BitVec.ofNat 32 value
          else 0xa5c300d2 ||| (BitVec.ofNat 32 value <<< 8) else 0x12345678
        let some (op,3) := X86Routine.decodeAt [0x80,UInt8.ofNat (0xc8+r),UInt8.ofNat mask] 0 | return false
        let some t := X86Routine.execute op ⟨⟨rs,fun _ => 0⟩,none,3⟩ | return false
        let v := BitVec.ofNat 8 (value ||| mask)
        let expected := if r<4 then 0xa5c3d200 ||| v.zeroExtend 32 else 0xa5c300d2 ||| (v.zeroExtend 32 <<< 8)
        if (List.range 8).any (fun k => t.core.regs (Fin.ofNat 8 k) != (if k==r%4 then expected else 0x12345678)) then return false
        let some flags := t.flags | return false
        if flags.zero != (v == 0) || flags.sign != v.msb || flags.overflow then return false
  return true

-- Store low/high bytes through memory operands, including a wrapping address.
#eval Id.run do
  for r in [:8] do
    for value in [:256] do
      for addr in ([0x1000,0x1001,0x1002,0xffffffff] : List Word) do
        let rs : Registers := fun k => if k=7 then addr else if k.val==r%4 then
          if r<4 then BitVec.ofNat 32 value else BitVec.ofNat 32 value <<< 8 else 0
        let bytes := [0x88,UInt8.ofNat (8*r+7)]
        let some (op,2) := X86Routine.decodeAt bytes 0 | return false
        let f := logical32 17
        let some t := X86Routine.execute op ⟨⟨rs,fun _ => 0xa5⟩,some f,2⟩ | return false
        if t.core.memory addr != BitVec.ofNat 8 value || t.core.memory (addr+1) != 0xa5 || t.core.memory (addr-1) != 0xa5 then return false
        if (List.range 8).any (fun k => t.core.regs (Fin.ofNat 8 k) != rs (Fin.ofNat 8 k)) then return false
        if t.flags != some f then return false
  return true

#eval [[0x80,0xc9],[0x80,0x09,0x40],[0x88],[0x88,0xc9]].all fun bytes =>
  (X86Routine.decodeAt bytes 0).isNone

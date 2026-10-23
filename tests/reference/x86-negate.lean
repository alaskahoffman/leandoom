import Doom.Verification.X86Routine
open Doom.Verification X86 X86Memory X86Control
#eval Id.run do
  for r in [:8] do
    let dst := Fin.ofNat 8 r
    if X86Routine.decodeAt [0xf7,UInt8.ofNat (0xd8+r)] 0 != some (.negateRegister dst,2) then return false
    for v in ([0,1,0x7fffffff,0x80000000,0xffffffff] : List Word) do
      let s : X86Control.State := ⟨⟨fun n => if n=dst then v else 123,fun _ => 0xa5⟩,some (compare32 7 8),0x100⟩
      let some t := X86Routine.execute (.negateRegister dst) s | return false
      if t.core.regs dst != -v || t.flags.isSome || t.pc != s.pc then return false
      for n in [:8] do
        if n != r && t.core.regs (Fin.ofNat 8 n) != s.core.regs (Fin.ofNat 8 n) then return false
      if t.core.memory 0x1234 != 0xa5 then return false
  for bytes in ([[0xf7],[0xf7,0x18],[0xf7,0x58,0x04],[0xf7,0x98,0,0,0,0],[0xf7,0xd0]] : List (List UInt8)) do
    if (X86Routine.decodeAt bytes 0).isSome then return false
  return true

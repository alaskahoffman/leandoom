import Doom.Proofs.OriginalWeaponLower
open Doom.Verification X86 X86Memory X86Control
-- CALL [ESP-4] must load the target before the return address overwrites it.
#eval Id.run do
  if X86Routine.decodeAt [0xff,0x51,0x0c] 0 != some (.callMemory ⟨some 1,none,0,12⟩,3) then return false
  for bytes in ([[0xff,0x51],[0xff,0xd1],[0xff,0x59,0x0c],[0xff,0x69,0x0c]] : List (List UInt8)) do
    if (X86Routine.decodeAt bytes 0).isSome then return false
  for sp in ([0,1,0x1000,0xffffffff] : List Word) do
    let memory := store32 (fun _ => 0xa5) (sp-4) 0x12345678
    let s : X86Control.State := ⟨⟨fun r => if r=4 then sp else 7,memory⟩,some (compare32 9 3),0x2468⟩
    let some t := X86Routine.execute (.callMemory ⟨some 4,none,0,-4⟩) s | return false
    if t.pc != 0x12345678 || t.core.regs 4 != sp-4 || load32 t.core.memory (sp-4) != 0x2468 then return false
    if t.flags != s.flags then return false
    for r in [:8] do
      if r != 4 && t.core.regs (Fin.ofNat 8 r) != s.core.regs (Fin.ofNat 8 r) then return false
    if (X86Routine.execute (.callMemory ⟨some 4,none,0,-4⟩) {s with pc := 4294967296}).isSome then return false
  return true

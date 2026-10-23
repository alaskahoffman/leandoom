import Doom.Proofs.InitializedAddress
open Doom.Verification Doom.Verification.X86Memory Doom.Proofs.InitializedAddress
-- Synthetic unit reads only; actual retained RAM is tested separately.
def raw : Memory := fun a => if a=0x100010 then 0x20 else if a=0x100012 then 0x10 else 0
def canon : Memory := fun a => if a=0x10 then 0x20 else 0
example : check raw canon 0x100000 0x200000 [.pointer 0x10 0x20] = true := by decide +kernel
example : check raw canon 0x100000 0x200000 [.scalar 0x10 0x20] = false := by decide +kernel
example : check raw canon 0x100001 0x200000 [.pointer 0x10 0x20] = false := by decide +kernel
example : check raw canon 0x100000 0x100012 [.pointer 0x10 0x20] = false := by decide +kernel
example : check raw canon 0x100000 0x200000 [.pointer 0xfffffff0 0] = false := by decide +kernel
example : check (fun _ => 0) (fun _ => 0) 0x100000 0x200000 [.pointer 0x10 0] = true := by decide +kernel
#check sound
#check pointer_translation
#check scalar_preserved
#check rows_sound
#check address_exact
#check pointer_reconstruct
example : rowsCheck 0x100000 0x200000 [(0x10,0x100020,0x20)] = true := by decide +kernel
example : rowsCheck 0x100000 0x200000 [(0x10,0x100020,0x21)] = false := by decide +kernel
example : rowsCheck 0x100000 0x200000 [(0x10,0,0)] = true := by decide +kernel
example : rowsCheck 0x100000 0x200000 [(0x100000010,0x100020,0x20)] = false := by decide +kernel

import Doom.Proofs.OriginalWeaponLower
open Doom.Verification X86 X86Memory X86Control
#eval Id.run do
  if X86Routine.decodeAt [0x66,0x83,0x42,0x0e,0x06] 0 != some (.addHalfImmediate ⟨some 2,none,0,14⟩ 6,5) then return false
  if (X86Routine.decodeAt [0x66,0x83,0x42,0x0e] 0).isSome then return false
  if (X86Routine.decodeAt [0x66,0x83,0x52,0x0e,0x06] 0).isSome then return false -- ADC
  if (X86Routine.decodeAt [0x66,0x83,0xc2,0x06] 0).isSome then return false -- unsupported register ADD16
  for imm in [:256] do
    let byte := UInt8.ofNat imm
    let mask := byte.toBitVec.signExtend 16
    if X86Routine.decodeAt [0x66,0x83,0x42,0x0e,byte] 0 != some (.addHalfImmediate ⟨some 2,none,0,14⟩ mask,5) then return false
    for address in ([0,1,0xffffffff] : List Word) do
      let m := X86Routine.store16 (fun _ => 0xa5) address 0xfffd
      let s : X86Control.State := ⟨⟨fun _ => address,m⟩,some (compare32 1 1),0⟩
      let some t := X86Routine.execute (.addHalfImmediate ⟨some 2,none,0,0⟩ mask) s | return false
      if load16 t.core.memory address != (0xfffd#16)+mask then return false
      if t.core.memory (address-1) != m (address-1) || t.core.memory (address+2) != m (address+2) then return false
      if t.flags.isSome then return false
  return true

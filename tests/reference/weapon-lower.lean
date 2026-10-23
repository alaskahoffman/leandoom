import Doom.Proofs.OriginalWeaponLower
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs WeaponLower
#eval Id.run do
  for raw in ([-2147483648,-2147483647,-65537,-1,0,1,32*65536,122*65536-1,122*65536,122*65536+1,128*65536,2147483647-6*65536,2147483647] : List Int32) do
    for offset in [:4] do
      for sp in ([0,1,4,0x4000,0xffffffff] : List Word) do
        let player : Word := 0x1000+BitVec.ofNat 32 offset
        let psp : Word := 0x2000+BitVec.ofNat 32 offset
        let m : Memory := fun _ => 0xa5
        let m := store32 (store32 (store32 m (player+4) 1) (psp+12) raw.toBitVec) sp 0x2d095
        let s : X86Memory.State := ⟨fun r => if r=0 then player else if r=2 then psp else if r=4 then sp else 0xabcdef01,m⟩
        let some t := X86Routine.run program [0x2d095] 9 ⟨s,none,0x2d490⟩ | return false
        if load32 t.core.memory (psp+12) != (Weapon.lowerHeight ⟨raw⟩ true).raw.toBitVec then return false
        if t.pc != 0x2d095 then return false
        for r in [:8] do
          let r : Reg := ⟨r%8,Nat.mod_lt _ (by decide)⟩
          if t.core.regs r != (if r=4 then sp+4 else s.regs r) then return false
        if load32 t.core.memory 0x3000 != load32 m 0x3000 then return false
  return true

-- The high-half update itself wraps; retain fractional bits at the carry edge.
#eval Id.run do
  for address in ([0,1,0xfffffffd,0xfffffffe,0xffffffff] : List Word) do
    for raw in ([0,0x1234ffff,0xfffaffff,0x7ffaffff,0xffffffff] : List Word) do
      let m := store32 (fun _ => 0xa5) address raw
      let after := X86Routine.store16 m (address+2) (load16 m (address+2)+6)
      if load32 after address != raw+0x60000 then return false
      if after (address-1) != m (address-1) || after (address+4) != m (address+4) then return false
  return true

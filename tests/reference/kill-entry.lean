import Doom.Proofs.OriginalKillEntry
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs KillEntry

def encoded (v : PlayerDamage.State) (d : Int32) (baby : Bool) (offset : Nat) : X86Memory.State := Id.run do
  let obj : Word := 0x1000+BitVec.ofNat 32 offset
  let p : Word := if offset % 2 = 0 then 0x2ae78 else 0x2000+BitVec.ofNat 32 offset
  let sp : Word := 0x4000+BitVec.ofNat 32 offset
  let mut m : Memory := fun _ => 0xa5
  m := store32 m 0x2923c 0
  m := store32 m 0x2b3dc 0
  m := store32 m (obj+132) p
  m := store32 m (obj+52) 0x3000
  m := store32 m 0x3000 0x3100
  m := store32 m (0x3100+14) 5
  m := store32 m (obj+104) (if v.shootable then 4 else 0)
  m := store32 m (obj+108) v.health.toBitVec
  m := store32 m (p+32) v.playerHealth.toBitVec
  m := store32 m (p+220) v.damageCount.toBitVec
  m := store32 m (p+228) 0x12345678
  m := store32 m (p+36) v.armor.toBitVec
  m := store32 m (p+40) v.armorType.toBitVec
  m := store32 m (p+196) (if v.god then 2 else 0)
  m := store32 m (p+44) (if v.invulnerable then 99 else 0)
  m := store32 m 0x2b3e0 (if baby then 0 else 4)
  return ⟨fun r => if r=0 then obj else if r=1 then d.toBitVec else if r=2 || r=3 then 0
    else if r=4 then sp else 0x10203040,m⟩

#eval Id.run do
  for pc in PlayerDamageEntry.sites do
    for offset in [0,1,2,3] do
      for baby in [false,true] do
        for damage in ([2,100,1000] : List Int32) do
          for tall in ([-2147483648,-7,-3,-1,0,1,3,4,56*65536,2147483647] : List Int32) do
            for flags in ([4,0x204,0x4004,0x100404,0xfeffffff,0x80000004,0x400004,0x1fffff] : List UInt32) do
              let flags := (flags &&& ~~~(0x1000000 : UInt32)) ||| 4
              let v : PlayerDamage.State := {sectorSpecial := 5,health := 1,playerHealth := 1}
              let s := encoded v damage baby offset
              let body : Death.Body := {flags,height := ⟨tall⟩}
              let s := {s with memory := store32 (store32 (store32 s.memory
                (s.regs 0+88) 0) (s.regs 0+104) flags.toBitVec) (s.regs 0+68) tall.toBitVec}
              let out := PlayerDamage.apply v damage none false baby {}
              if !out.killed then return false
              let some t := X86Routine.run joined exits 131 ⟨s,none,pc⟩ | return false
              if observation s t != liveObservation out body then return false
              if t.pc != 0x2a2e6 || t.core.regs 1 != 0 || t.core.regs 3 != s.regs 0 || t.core.regs 4 != s.regs 4-52 then return false
              if load32 t.core.memory (s.regs 4-32) != 0x2a6b1 then return false
              if load32 t.core.memory 0x12720 != load32 s.memory 0x12720 then return false
  return true

-- CALL/prologue saves use actual wrapping byte addresses.
#eval Id.run do
  for sp in ([0,1,2,3,16,31,52,0xffffffff] : List Word) do
    let v : PlayerDamage.State := {sectorSpecial := 5,health := 1,playerHealth := 1}
    let s := encoded v 5 false 1
    let s := {s with regs := write s.regs 4 sp}
    let s := {s with memory := store32 (store32 s.memory (s.regs 0+88) 0) (s.regs 0+68) 0xffffffff}
    let some t := X86Routine.run joined exits 131 ⟨s,none,0x2fb76⟩ | return false
    if t.core.regs 4 != sp-52 then return false
    if load32 t.core.memory (sp-32) != 0x2a6b1 then return false
    if load32 t.core.memory (s.regs 0+68) != 0xffffffff then return false
  return true

-- The lost-soul type takes the other gravity branch. This certificate's live
-- player relation must not silently admit that metadata.
#eval Id.run do
  let s := encoded {sectorSpecial := 5} 5 false 1
  let obj := s.regs 0
  let s := {s with regs := write (write s.regs 2 obj) 3 obj}
  let s := {s with memory := store32 (store32 (store32 s.memory
    (obj+88) 18) (obj+104) 0x204) (obj+68) 100}
  let some t := X86Routine.run program [0x2a2e6] 13 ⟨s,none,0x2a2b9⟩ | return false
  if load32 t.core.memory (obj+104) != 0x100600 then return false
  if load32 t.core.memory (obj+68) != 25 then return false
  return true

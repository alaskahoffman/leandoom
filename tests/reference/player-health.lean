import Doom.Proofs.OriginalPlayerHealth
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs PlayerHealth

def encoded (v : PlayerDamage.State) (d : Int32) (baby : Bool) (offset : Nat) : X86Memory.State := Id.run do
  let obj : Word := 0x1000+BitVec.ofNat 32 offset
  let p : Word := 0x2000+BitVec.ofNat 32 offset
  let sp : Word := 0x4000+BitVec.ofNat 32 offset
  let mut m : Memory := fun _ => 0xa5
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

def checks : Bool := Id.run do
  for pc in PlayerDamageEntry.sites do
    for offset in [0,1,2,3] do
      for damage in ([-2147483648,5,10,20,999,1000,1999,2000,2147483647] : List Int32) do
        for health in ([-1,0,1,100] : List Int32) do
          for shootable in [false,true] do
            for god in [false,true] do
              for invulnerable in [false,true] do
                for baby in [false,true] do
                  let v : PlayerDamage.State := {health,shootable,god,invulnerable,armor := 6,armorType := 1,sectorSpecial := 5,playerHealth := damage,damageCount := damage+99}
                  let s := encoded v damage baby offset
                  let some t := X86Routine.run joined [0x2a650,0x2a747] 73 ⟨s,none,pc⟩ | return false
                  if observation s t != liveObservation v (PlayerDamage.apply v damage none false baby {}) then return false
                  if t.core.regs 4 != s.regs 4-28 || t.core.regs 6 != s.regs 0 then return false
                  if load32 t.core.memory (s.regs 4-4) != BitVec.ofNat 32 (pc+5) then return false
                  if load32 t.core.memory (s.regs 4-28) != 0 || load32 t.core.memory (s.regs 4-24) != 0 then return false
                  if t.core.memory 0x5000 != 0xa5 then return false
  return true

#eval checks

-- A source local overlapping player.health observes the post-subtraction word.
-- This validates instruction order and demonstrates why the seam needs separation.
#eval Id.run do
  let v : PlayerDamage.State := {playerHealth := 100,damageCount := 0}
  let s := encoded v 20 false 0
  let p := PlayerDamageEntry.inputPlayer s
  let s := {s with regs := write (write (write s.regs 5 p) 7 20) 4 (p+28)}
  let some t := X86Routine.run PlayerHealth.program [0x2a650] 14 ⟨s,none,0x2a616⟩ | return false
  return load32 t.core.memory (p+32) == 80 && load32 t.core.memory (p+228) == 80

-- Arbitrary source pointers survive the standalone block, including zero damage.
#eval Id.run do
  for source in ([0,1,0x12345678,0xffffffff] : List Word) do
    for damage in ([0,20,0x80000000,0x7fffffff] : List Word) do
      let v : PlayerDamage.State := {playerHealth := 100,damageCount := 99}
      let s := encoded v 0 false 0
      let p := PlayerDamageEntry.inputPlayer s
      let s := {s with
        regs := write (write s.regs 5 p) 7 damage,
        memory := store32 s.memory (s.regs 4+4) source}
      let some t := X86Routine.run PlayerHealth.program [0x2a650] 14 ⟨s,none,0x2a616⟩ | return false
      if load32 t.core.memory (p+228) != source then return false
  return true

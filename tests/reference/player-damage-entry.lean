import Doom.Proofs.OriginalPlayerDamageEntry
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs PlayerDamageEntry

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
  m := store32 m (p+36) v.armor.toBitVec
  m := store32 m (p+40) v.armorType.toBitVec
  m := store32 m (p+196) (if v.god then 2 else 0)
  m := store32 m (p+44) (if v.invulnerable then 99 else 0)
  m := store32 m 0x2b3e0 (if baby then 0 else 4)
  return ⟨fun r => if r=0 then obj else if r=1 then d.toBitVec else if r=2 || r=3 then 0
    else if r=4 then sp else 0x10203040,m⟩

def checks : Bool := Id.run do
  for pc in sites do
    for offset in [0,1,2,3] do
      for damage in ([-2147483648,5,10,20,999,1000,1999,2000,2147483647] : List Int32) do
        for health in ([-1,0,1,100] : List Int32) do
          for shootable in [false,true] do
            for god in [false,true] do
              for invulnerable in [false,true] do
                for baby in [false,true] do
                  let v : PlayerDamage.State := {health,shootable,god,invulnerable,armor := 6,armorType := 1,sectorSpecial := 5}
                  let s := encoded v damage baby offset
                  let some t := X86Routine.run program [0x2a616,0x2a747] 59 ⟨s,none,pc⟩ | return false
                  if observation s t != liveObservation v (PlayerDamage.apply v damage none false baby {}) then return false
                  if t.core.regs 4 != s.regs 4-28 || t.core.regs 6 != s.regs 0 then return false
                  if load32 t.core.memory (s.regs 4-4) != BitVec.ofNat 32 (pc+5) then return false
                  if load32 t.core.memory (s.regs 4-28) != 0 || load32 t.core.memory (s.regs 4-24) != 0 then return false
                  if t.core.memory 0x5000 != 0xa5 then return false
  return true

#eval checks
#eval X86Routine.decode [0x0f,0x8e,0xc2,0x02,0,0] == some (.jumpSigned 1 706,[])
#eval X86Routine.decode [0x0f,0x8e,0xc2] == none

-- Overlapping the real stack locals with armor destroys the initial encoding.
-- This is a witness that the stack-separation premise cannot be ignored.
#eval Id.run do
  let v : PlayerDamage.State := {armor := 6,armorType := 1,sectorSpecial := 5}
  let s := encoded v 20 false 0
  let s := {s with regs := write s.regs 4 (inputPlayer s+64)}
  let some t := X86Routine.run program [0x2a616,0x2a747] 59 ⟨s,none,0x2fbd2⟩ | return false
  return observation s t != liveObservation v (PlayerDamage.apply v 20 none false false {})

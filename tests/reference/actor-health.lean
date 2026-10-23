import Doom.Proofs.OriginalActorHealth
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs ActorHealth

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
                  let some t := X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,none,pc⟩ | return false
                  if observation s t != liveObservation v (PlayerDamage.apply v damage none false baby {}) then return false
                  if t.core.regs 4 != s.regs 4-28 || t.core.regs 6 != s.regs 0 then return false
                  if load32 t.core.memory (s.regs 4-4) != BitVec.ofNat 32 (pc+5) then return false
                  if load32 t.core.memory (s.regs 4-28) != 0 || load32 t.core.memory (s.regs 4-24) != 0 then return false
                  if t.core.memory 0x5000 != 0xa5 then return false
  return true

#eval checks

-- The supported device-disabled path must not silently handle an enabled device.
#eval Id.run do
  let v : PlayerDamage.State := {sectorSpecial := 5}
  let s := encoded v 20 false 0
  let s := {s with memory := store32 s.memory 0x2923c 1}
  return (X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,none,0x2fbd2⟩).isNone

-- A stack push overlapping the device flag invalidates the initial zero setting.
#eval Id.run do
  let v : PlayerDamage.State := {sectorSpecial := 5}
  let s := encoded v 20 false 0
  let s := {s with regs := write s.regs 4 (0x2923c+32)}
  return (X86Routine.run joined [0x2a6a6,0x2a6b6,0x2a747] 108 ⟨s,none,0x2fbd2⟩).isNone

-- A zero-health result takes the death continuation; negative health is retained.
#eval Id.run do
  for hp in ([0,1,100,-1,-2147483648,2147483647] : List Int32) do
    for dmg in ([0,1,100,-1,-2147483648,2147483647] : List Int32) do
      let v : PlayerDamage.State := {health := hp,sectorSpecial := 5}
      let s := encoded v dmg false 1
      let s := {s with regs := write (write (write s.regs 6 (s.regs 0)) 7 dmg.toBitVec) 5 0}
      let some t := X86Routine.run program [0x2a6a6,0x2a6b6] 35 ⟨s,none,0x2a650⟩ | return false
      if load32 t.core.memory (s.regs 0+108) != (hp-dmg).toBitVec then return false
      if (t.pc == 0x2a6a6) != decide (hp-dmg ≤ 0) then return false
  return true

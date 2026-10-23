import Doom.Proofs.OriginalPlayerPain
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs PlayerPain

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

def seeded (s : X86Memory.State) (i : UInt8) : X86Memory.State :=
  let m : Memory := fun a => if 0x1261c ≤ a.toNat ∧ a.toNat < 0x1271c then
    Doom19.randomTableBytes.toArray[a.toNat-0x1261c]!.toBitVec else s.memory a
  {s with memory := store32 (store32 (store32 (store32 m
    (s.regs 0+92) 0x6000) (0x6000+32) 255) 0x12720 (BitVec.ofNat 32 i.toNat)) 0x1271c 197}

def apart (a b : Word) : Bool := (List.range 4).all fun i => (List.range 4).all fun j =>
  a+BitVec.ofNat 32 i != b+BitVec.ofNat 32 j

-- Every RNG index, all CALL sites, both tactile cases, every byte alignment,
-- accepted-surviving, accepted-lethal and rejected damage.
#eval Id.run do
  for n in [:256] do
    for pc in PlayerDamageEntry.sites do
      for offset in [0,1,2,3] do
        for pair in ([(5,true),(100,true),(5,false)] : List (Int32 × Bool)) do
          let (damage,shootable) := pair
          let i := UInt8.ofNat n
          let v : PlayerDamage.State := {shootable,sectorSpecial := 5}
          let s := seeded (encoded v damage false offset) i
          let some t := X86Routine.run joined exits 121 ⟨s,none,pc⟩ | return false
          if observation s t != liveObservation v (PlayerDamage.apply v damage none false false {play := i,misc := 197}) then return false
          if load32 t.core.memory 0x1271c != 197 then return false
          if t.core.regs 4 != s.regs 4-28 || t.core.regs 6 != s.regs 0 then return false
          if !(prefixReads s i).all (fun a => (ActorHealth.joinedWrites s).all (apart a)) then return false
          if !(suffixReads s i).all (fun a => (suffixWrites s).all (apart a)) then return false
  return true

-- General machine decision theorem: all rolls, signed threshold edges and
-- both skull-flight flags. This block intentionally makes no RNG call.
#eval Id.run do
  for n in [:256] do
    for chance in ([-2147483648,-1,0,1,254,255,256,2147483647] : List Int32) do
      for skull in [false,true] do
        let m : Memory := fun _ => 0
        let m := store32 (store32 m (0x6000+32) chance.toBitVec) (0x1000+104) (if skull then 0x01000000 else 0)
        let s : X86Memory.State := ⟨fun r => if r=0 then BitVec.ofNat 32 n else if r=2 then 0x6000 else if r=6 then 0x1000 else 0,m⟩
        let some t := X86Routine.run program [0x2a6c9,0x2a6df] 4 ⟨s,none,0x2a6be⟩ | return false
        if (t.pc == 0x2a6c9) != (decide ((n:Int)<chance.toInt) && !skull) then return false
  return true

-- Corrupt table data is read from memory, rather than replaced by a host RNG.
#eval Id.run do
  let s := seeded (encoded {sectorSpecial := 5} 5 false 0) 0
  let m : Memory := fun a => if a=0x1261d then 255 else s.memory a
  let s := {s with memory := m}
  let some t := X86Routine.run joined exits 121 ⟨s,none,0x2fbd2⟩ | return false
  return t.pc == 0x2a6df && load32 t.core.memory 0x12720 == 1

-- If the return slot aliases the RNG index, its actual write changes RET.
#eval Id.run do
  let s := seeded (encoded {sectorSpecial := 5} 5 false 0) 0
  let s := {s with regs := write (write s.regs 6 (s.regs 0)) 4 (0x12720+4)}
  return (X86Routine.run program [0x2a6c9,0x2a6df] 13 ⟨s,none,0x2a6b6⟩).isNone

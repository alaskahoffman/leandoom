import Doom.Proofs.OriginalDamageReturn
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs DamageReturn

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
  let m : Memory := fun a => if 0x16b38 ≤ a.toNat ∧ a.toNat < 0x16b54 then
    PainSetter.painStateBytes.toArray[a.toNat-0x16b38]!.toBitVec else m a
  let m := store32 m (s.regs 0+88) 0
  let m := store32 m (s.regs 0+124) (BitVec.ofNat 32 i.toNat - 128)
  let m := store32 m (s.regs 0+128) (if i.toNat%2=0 then 0 else 100)
  let m := store32 m (0x6000+28) 156
  {s with memory := store32 (store32 (store32 (store32 m
    (s.regs 0+92) 0x6000) (0x6000+32) 255) 0x12720 (BitVec.ofNat 32 i.toNat)) 0x1271c 197}

def apart (a b : Word) : Bool := (List.range 4).all fun i => (List.range 4).all fun j =>
  a+BitVec.ofNat 32 i != b+BitVec.ofNat 32 j

-- Initial flag may already be set; unrelated high and low flag bits survive.
#eval Id.run do
  for offset in [0,1,2,3] do
    let s := seeded (encoded {sectorSpecial := 5} 5 false offset) 0
    if !(savedReads s).all (fun a => (PainSetter.afterWrites s).all (apart a)) then return false
    if !(savedReads s ++ retained s).all (fun a => apart a (s.regs 0+124)) then return false
    if !(PainSetter.joinedWrites s).all (apart (s.regs 0+88)) then return false
  for n in [:256] do
    for pc in PlayerDamageEntry.sites do
      for offset in [0,1,2,3] do
        for pair in ([(5,true),(0,true),(-1,true)] : List (Int32 × Bool)) do
          let (damage,shootable) := pair
          let i := UInt8.ofNat n
          let v : PlayerDamage.State := {shootable,sectorSpecial := 5}
          let s := seeded (encoded v damage false offset) i
          let initial := load32 s.memory (s.regs 0+104) ||| (if n%2=0 then (0xa4000040#32) else (0x44000000#32))
          let s := {s with memory := store32 s.memory (s.regs 0+104) initial}
          let out := PlayerDamage.apply v damage none false false {play := i,misc := 197}
          let some t := X86Routine.run joined exits 166 ⟨s,none,pc⟩ | return false
          if observation s t != liveObservation s out then return false
          if t.pc != pc+5 then return false
          if !([4,5,6,7] : List Reg).all (fun r => t.core.regs r == s.regs r) then return false
  return true



-- The tail reads its saved return address through real memory. A source pointer
-- that would require retargeting cannot be silently treated as null.
#eval Id.run do
  let s := seeded (encoded {sectorSpecial := 5} 5 false 0) 0
  let s := {s with regs := write s.regs 6 (s.regs 0)}
  let m := store32 (store32 (store32 (store32 (store32 s.memory
    (s.regs 4+4) 0) (s.regs 4+12) 11) (s.regs 4+16) 22) (s.regs 4+20) 33) (s.regs 4+24) 0x2fb7b
  let s := {s with memory := m}
  let some t := X86Routine.run program [0x2fb7b] 14 ⟨s,none,0x2a6df⟩ | return false
  if t.pc != 0x2fb7b || t.core.regs 4 != s.regs 4+28 then return false
  if t.core.regs 5 != 11 || t.core.regs 7 != 22 || t.core.regs 6 != 33 then return false
  let bad := {s with memory := store32 s.memory (s.regs 4+4) 0x1800}
  if (X86Routine.run program [0x2fb7b] 14 ⟨bad,none,0x2a6df⟩).isSome then return false
  let bad := {s with memory := store32 s.memory (s.regs 4+24) 0xdeadbeef}
  if (X86Routine.run program [0x2fb7b] 14 ⟨bad,none,0x2a6df⟩).isSome then return false
  return true


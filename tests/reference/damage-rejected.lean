import Doom.Proofs.OriginalDamageRejected
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs DamageRejected

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

-- Both sides of the nonlethal theorem, including retained attacker pointers.
#eval Id.run do
  for offset in [0,1,2,3] do
    let s := seeded (encoded {sectorSpecial := 5} 5 false offset) 0
    if !(reads s).all (fun a => (PlayerDamageEntry.slots s).all (apart a)) then return false
  for n in [:256] do
    for pc in PlayerDamageEntry.sites do
      for offset in [0,1,2,3] do
        for v in ([{sectorSpecial := 5}, {sectorSpecial := 5,shootable := false},
                   {sectorSpecial := 5,health := 0}, {sectorSpecial := 5,god := true},
                   {sectorSpecial := 5,invulnerable := true}] : List PlayerDamage.State) do
          let i := UInt8.ofNat n
          let baby := n%2==0
          let s := seeded (encoded v 5 baby offset) i
          let out := PlayerDamage.apply v 5 none false baby {play := i,misc := 197}
          let some t := X86Routine.run DamageReturn.joined DamageReturn.exits 166 ⟨s,none,pc⟩ | return false
          if out.killed || observation s t != liveObservation s out then return false
          if t.pc != pc+5 then return false
          if !([4,5,6,7] : List Reg).all (fun r => t.core.regs r == s.regs r) then return false
          if !out.applied then
            if load32 t.core.memory (s.regs 0+124) != load32 s.memory (s.regs 0+124) then return false
            if load32 t.core.memory (PlayerDamageEntry.inputPlayer s+228) != 0x12345678 then return false
            if load32 t.core.memory 0x12720 != BitVec.ofNat 32 n then return false
  return true

-- Rejection does not read the pain info, animation table, random table, or
-- tactile-device metadata: leave these as poison, with no seeded initializer.
-- Include a wrapping stack as well as the four ordinary alignments.
#eval Id.run do
  for offset in [0,1,2,3] do
    for pc in PlayerDamageEntry.sites do
      for stack in ([0,1,2,3,0x4000] : List Word) do
        for v in ([{sectorSpecial := 5,shootable := false}, {sectorSpecial := 5,health := -1},
                   {sectorSpecial := 5,god := true}, {sectorSpecial := 5,invulnerable := true}] : List PlayerDamage.State) do
          let s := encoded v 5 false offset
          let s := {s with regs := write s.regs 4 stack}
          let some t := X86Routine.run DamageReturn.joined DamageReturn.exits 40 ⟨s,none,pc⟩ | return false
          if t.pc != pc+5 then return false
          if !([4,5,6,7] : List Reg).all (fun r => t.core.regs r == s.regs r) then return false
          let saved := PlayerDamageEntry.saved s pc
          for a in PlayerDamageEntry.slots s ++ reads s do
            if load32 t.core.memory a != load32 saved a then return false
  return true

-- Damage 1000 bypasses protection, but the baby-skill shift happens first.
#eval Id.run do
  for baby in [false,true] do
    for d in ([999,1000,1999,2000] : List Int32) do
      for pc in PlayerDamageEntry.sites do
        let v : PlayerDamage.State := {sectorSpecial := 5,health := 3000,playerHealth := 3000,god := true,invulnerable := true}
        let s := seeded (encoded v d baby 0) 255
        let out := PlayerDamage.apply v d none false baby {play := 255,misc := 197}
        if out.applied != ((if baby then d >>> 1 else d) ≥ 1000) then return false
        let some t := X86Routine.run DamageReturn.joined DamageReturn.exits 166 ⟨s,none,pc⟩ | return false
        if out.killed || observation s t != liveObservation s out then return false
  return true

-- Stack separation is substantive: when a saved register overlaps the old
-- attacker slot, the machine preserves its real stack write, not the old value.
#eval Id.run do
  let v : PlayerDamage.State := {sectorSpecial := 5,shootable := false}
  let s := encoded v 5 false 1
  let attacker := PlayerDamageEntry.inputPlayer s+228
  let s := {s with regs := write s.regs 4 (attacker+8)}
  if (reads s).all (fun a => (PlayerDamageEntry.slots s).all (apart a)) then return false
  let some t := X86Routine.run DamageReturn.joined DamageReturn.exits 40 ⟨s,none,0x2fb76⟩ | return false
  if load32 t.core.memory attacker != s.regs 6 then return false
  if load32 t.core.memory attacker == load32 s.memory attacker then return false
  return true

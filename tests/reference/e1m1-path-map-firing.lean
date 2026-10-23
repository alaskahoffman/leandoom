import Doom.Proofs.E1M1PathMapFiring
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1DischargeSetters
namespace PathMapFiringFixture
def pistolData : Array UInt8 := #[3,0,0,0,1,0,0,0,6,0,0,0,144,216,2,0,15,0,0,0,0,0,0,0,0,0,0,0]
def shotgunData : Array UInt8 := #[1,0,0,0,0,0,0,0,7,0,0,0,16,217,2,0,23,0,0,0,0,0,0,0,0,0,0,0]
def weaponsData : Array UInt8 := #[5,0,0,0,4,0,0,0,3,0,0,0,2,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,11,0,0,0,10,0,0,0,13,0,0,0,17,0,0,0,1,0,0,0,20,0,0,0,19,0,0,0,18,0,0,0,21,0,0,0,30,0,0,0]
def pistolflashData : Array UInt8 := #[4,0,0,0,0,128,0,0,7,0,0,0,80,219,2,0,1,0,0,0,0,0,0,0,0,0,0,0]
def shotgunflash1Data : Array UInt8 := #[5,0,0,0,0,128,0,0,4,0,0,0,80,219,2,0,31,0,0,0,0,0,0,0,0,0,0,0]
def poseData : Array UInt8 := #[28,0,0,0,5,128,0,0,6,0,0,0,0,0,0,0,154,0,0,0,0,0,0,0,0,0,0,0]
def base : Word := 0x900003
def lines : Word := 0x700001
def words : Array Nat := #[0,0,36,23,5,0,0,474,65535]
def mapMemory : Memory :=
  [(base,0),(base+4,23*65536+36),(base+8,5),(base+12,474*65536),(base+16,65535),
   (0x2c100,base+8),(0x2c10c,base),(0x2c120,lines),(0x2c0fc,36),(0x2c110,23)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def tableMemory : Memory := fun a =>
  if 89008 ≤ a.toNat ∧ a.toNat < 89036 then pistolData[a.toNat-89008]!.toBitVec else
  if 89232 ≤ a.toNat ∧ a.toNat < 89260 then shotgunData[a.toNat-89232]!.toBitVec else
  if 77200 ≤ a.toNat ∧ a.toNat < 77272 then weaponsData[a.toNat-77200]!.toBitVec else
  if 89092 ≤ a.toNat ∧ a.toNat < 89120 then pistolflashData[a.toNat-89092]!.toBitVec else
  if 89456 ≤ a.toNat ∧ a.toNat < 89484 then shotgunflash1Data[a.toNat-89456]!.toBitVec else
  if 92956 ≤ a.toNat ∧ a.toNat < 92984 then poseData[a.toNat-92956]!.toBitVec else
  mapMemory a
def p : Word := 0x600043
def obj : Word := 0x600401
def context (gun : Fire.Gun) (ammo : Int32) : Weapon.Context :=
  {state := {weapon := {frame := WeaponActions.windup gun,tics := 1}},
   player := {ammo := #v[ammo,ammo,77,88]}}
def machine (gun : Fire.Gun) (ammo : Int32) : X86Memory.State :=
  {regs := fun r => if r=1 then p else if r=4 then 1 else 0,
   memory := store32 (store32 (store32 (store32 tableMemory p obj)
     (p+112) (OriginalWeaponDischarge.weaponNumber gun)) (p+156) ammo.toBitVec) (p+160) ammo.toBitVec}
-- These are diagnostic machine states, not assertions of reachable E1M1 states.
-- Both guns, positive ammo and the two signed/wrapping boundaries.
def gunOf (i : Fin 4) : Fire.Gun := if i.val%2=0 then .pistol else .shotgun
def ammoOf (i : Fin 4) : Int32 := if i=0 then 0 else if i=1 then -2147483648 else 8

theorem inputs (i : Fin 4) : Inputs (gunOf i) (machine (gunOf i) (ammoOf i)) (context (gunOf i) (ammoOf i)) := by
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases choices with rfl|rfl|rfl|rfl <;> constructor
  all_goals (repeat' constructor)
  all_goals try simp only [debitReads,poseWrites,beforeFlashWrites,afterPoseWrites,flashReads,
    DeathSetter.tableWords,DeathSetter.writes,DeathSetter.fields,PainSetter.fields,E1M1FlashInstall.writes,
    List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,or_imp,forall_and]
  all_goals (repeat' constructor) <;> first
    | decide +kernel
    | (unfold Apart; decide +kernel)
    | (unfold E1M1FlashInstall.Separated Apart; decide +kernel)

example (i : Fin 4) : ∃ n, n≤116 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
    ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
      (flashed (gunOf i) (machine (gunOf i) (ammoOf i))) ∧
    Agrees (gunOf i) (machine (gunOf i) (ammoOf i)) (context (gunOf i) (ammoOf i))
      (flashed (gunOf i) (machine (gunOf i) (ammoOf i))) :=
  live_joined _ _ _ _ (inputs i)
example : load32 (flashed .pistol (machine .pistol 0)).core.memory (p+156)=0xffffffff := by decide +kernel
example : load32 (flashed .shotgun (machine .shotgun (-2147483648))).core.memory (p+160)=0x7fffffff := by decide +kernel
example : load32 (flashed .pistol (machine .pistol 8)).core.memory (p+264)=7 := by decide +kernel
example : load32 (flashed .shotgun (machine .shotgun 8)).core.memory (p+264)=4 := by decide +kernel
example : (flashed .shotgun (machine .shotgun 8)).pc=0x2d966 := by decide +kernel

open E1M1PathMap E1M1PathMapFiring

def destinations : List Word :=
  [0x1,0xfffffffd,0xfffffff9,0xfffffff5,0xfffffff1,0xffffffed,0xffffffe9,0xffffffe5,0xffffffe1,0xffffffdd,0xffffffd9,0xffffffd5,0xffffffd1,0xffffffcd,0xffffffc9,0xffffffc5,0xffffffc1,0xffffffbd,0xffffffb9,0xffffffb5,0xffffffb1,0xffffffad,0xffffffa9,0xffffffa5,0xffffffa1,0xffffff9d,0xffffff99,0xffffff95,0xffffff91,0xffffff8d,0xffffff89,0xffffff85,0xffffff81] ++
  [obj+100,obj+96,obj+36,obj+40,p+156,p+160,p+260,p+264,p+232,
   0x2b9ac,0x2b9b8,0x2b9f8,0x2b9a8,0x2c1e4,0x2c1e8,
   0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c]

theorem safe_of_destinations (i : Fin 4) (a : Word)
    (h : ∀ b∈destinations, Apart a b) : Safe (gunOf i) (machine (gunOf i) (ammoOf i)) a := by
  repeat' constructor
  all_goals try simp [beforeFlashWrites,poseWrites,DeathSetter.writes,DeathSetter.fields,
    PainSetter.fields,E1M1FlashInstall.writes,slopeWrites,OriginalBulletSlope.saveWrites,
    OriginalAimQuery.saveWrites,OriginalAimSetup.writes,E1M1PathMapSetup.Safe,
    OriginalPathInit.writes,E1M1PathMapSetup.StackSafe,E1M1PathMapSetup.offsets,
    List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,or_imp,forall_and]
  all_goals (repeat' constructor)
  all_goals try simp only [E1M1PathMapSetup.StackSafe,E1M1PathMapSetup.offsets,
    List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_eq]
  all_goals (repeat' constructor)
  all_goals apply h
  all_goals revert i; decide +kernel

theorem safe_globals (i : Fin 4) :
    ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120],
      Safe (gunOf i) (machine (gunOf i) (ammoOf i)) a := by
  have finite : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120],
      ∀ b∈destinations, Apart a b := by
    simp only [destinations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_eq,forall_eq_or_imp,forall_and]
    repeat' constructor
    all_goals unfold Apart; decide +kernel
  exact fun a ha => safe_of_destinations i a (finite a ha)

theorem safe_image (i : Fin 4) : ∀ k<words.size,
    Safe (gunOf i) (machine (gunOf i) (ammoOf i)) (base+BitVec.ofNat 32 (2*k)) := by
  have finite : ∀ k : Fin 9, ∀ b∈destinations, Apart (base+BitVec.ofNat 32 (2*k.val)) b := by
    simp only [destinations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_eq,forall_and]
    repeat' constructor
    all_goals unfold Apart; decide +kernel
  exact fun k hk => safe_of_destinations i _ (finite ⟨k,hk⟩)

theorem image (i : Fin 4) : WordImage (machine (gunOf i) (ammoOf i)).memory base words := by
  intro k value h
  have bound : k<9 := (Array.getElem?_eq_some_iff.mp h).1
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases cases with h0|h0|h0|h0|h0|h0|h0|h0|h0
  all_goals subst k; simp [words] at h; subst value; revert i; decide +kernel

theorem map_inputs (i : Fin 4) :
    MapInputs (gunOf i) (machine (gunOf i) (ammoOf i)) base lines words 36 23 := by
  refine ⟨?_,?_,by decide,by decide,?_,?_,?_,safe_globals i,image i,safe_image i⟩
  all_goals revert i; decide +kernel

theorem joined (i : Fin 4) :
    (∃ n≤127, X86CodeMemory.Prefix FloorCaller.cm E1M1BulletAim.program [] n
      ⟨machine (gunOf i) (ammoOf i),none,OriginalWeaponDischarge.afterSound (gunOf i)⟩
      (E1M1BulletAim.firstQuery (gunOf i) (machine (gunOf i) (ammoOf i)))) ∧
    E1M1PathMapQuery.MapInputs
      (E1M1BulletAim.firstQuery (gunOf i) (machine (gunOf i) (ammoOf i))).core base lines words 36 23 :=
  query_execution _ _ _ _ (inputs i) _ _ _ _ _ (map_inputs i)

example : (E1M1BulletAim.firstQuery .pistol (machine .pistol 8)).core.regs 4=(0xffffffe9#32) := by decide +kernel
example : load32 (E1M1BulletAim.firstQuery .shotgun (machine .shotgun 8)).core.memory
    0xffffffe9=(0x2d7d5#32) := by decide +kernel
#print axioms joined
end PathMapFiringFixture

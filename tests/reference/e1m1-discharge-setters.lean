import Doom.Proofs.E1M1DischargeSetters
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1DischargeSetters
namespace DischargeSettersFixture
def pistolData : Array UInt8 := #[3,0,0,0,1,0,0,0,6,0,0,0,144,216,2,0,15,0,0,0,0,0,0,0,0,0,0,0]
def shotgunData : Array UInt8 := #[1,0,0,0,0,0,0,0,7,0,0,0,16,217,2,0,23,0,0,0,0,0,0,0,0,0,0,0]
def weaponsData : Array UInt8 := #[5,0,0,0,4,0,0,0,3,0,0,0,2,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,11,0,0,0,10,0,0,0,13,0,0,0,17,0,0,0,1,0,0,0,20,0,0,0,19,0,0,0,18,0,0,0,21,0,0,0,30,0,0,0]
def pistolflashData : Array UInt8 := #[4,0,0,0,0,128,0,0,7,0,0,0,80,219,2,0,1,0,0,0,0,0,0,0,0,0,0,0]
def shotgunflash1Data : Array UInt8 := #[5,0,0,0,0,128,0,0,4,0,0,0,80,219,2,0,31,0,0,0,0,0,0,0,0,0,0,0]
def poseData : Array UInt8 := #[28,0,0,0,5,128,0,0,6,0,0,0,0,0,0,0,154,0,0,0,0,0,0,0,0,0,0,0]
def tableMemory : Memory := fun a =>
  if 89008 ≤ a.toNat ∧ a.toNat < 89036 then pistolData[a.toNat-89008]!.toBitVec else
  if 89232 ≤ a.toNat ∧ a.toNat < 89260 then shotgunData[a.toNat-89232]!.toBitVec else
  if 77200 ≤ a.toNat ∧ a.toNat < 77272 then weaponsData[a.toNat-77200]!.toBitVec else
  if 89092 ≤ a.toNat ∧ a.toNat < 89120 then pistolflashData[a.toNat-89092]!.toBitVec else
  if 89456 ≤ a.toNat ∧ a.toNat < 89484 then shotgunflash1Data[a.toNat-89456]!.toBitVec else
  if 92956 ≤ a.toNat ∧ a.toNat < 92984 then poseData[a.toNat-92956]!.toBitVec else
  0
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
end DischargeSettersFixture

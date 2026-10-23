import Doom.Proofs.E1M1AimSetup
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace AimSetupFixture
open OriginalAimSetup
def thing : Collision.SolidThing :=
  { x:=⟨2147483647⟩,y:=⟨-2147483648⟩,z:=⟨-1⟩,height:=⟨-3⟩,radius:=⟨0⟩ }
def angle : Angle := ⟨0⟩
def distance : Fixed := Fixed.ofInt 1024
def obj : Word := 0x600043
def machine : X86Memory.State :=
  {regs := fun r => if r=0 then obj else if r=1 then
      (thing.attackEndpoint angle distance).1.raw.toBitVec-thing.x.raw.toBitVec
    else if r=6 then (thing.attackEndpoint angle distance).2.raw.toBitVec-thing.y.raw.toBitVec
    else if r=3 then distance.raw.toBitVec else if r=4 then 1 else 0x12345678,
   memory:=store32 (store32 (store32 (store32 (fun _ => 0)
      (obj+12) thing.x.raw.toBitVec) (obj+16) thing.y.raw.toBitVec)
      (obj+20) thing.z.raw.toBitVec) (obj+68) thing.height.raw.toBitVec}
-- Diagnostic boundary state; not asserted reachable in E1M1.
theorem inputs : Inputs machine thing angle distance := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change (thing.x.raw.toBitVec+((thing.attackEndpoint angle distance).1.raw.toBitVec-thing.x.raw.toBitVec),
      thing.y.raw.toBitVec+((thing.attackEndpoint angle distance).2.raw.toBitVec-thing.y.raw.toBitVec))=
      ((thing.attackEndpoint angle distance).1.raw.toBitVec,(thing.attackEndpoint angle distance).2.raw.toBitVec)
    have cancel (a b : Word) : a+(b-a)=b := by rw [BitVec.add_comm,BitVec.sub_add_cancel]
    rw [cancel,cancel]
  · change ∀ (a : Word), a ∈ [obj+12,obj+16,obj+20,obj+68] → ∀ (b : Word),
      b ∈ [(0xfffffffd : Word),0x2b9ac,0x2b9b8,0xfffffff9,0x2b9f8,0x2b9a8,0x2c1e4,0x2c1e8,0xfffffff5] → Apart a b
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_imp,
      forall_eq_or_imp,forall_eq,forall_and]
    repeat' constructor
    all_goals unfold Apart
    all_goals decide +kernel
  · unfold Separated Apart
    decide +kernel

example : Ready machine (traversal machine) thing angle distance := ready _ _ _ _ inputs
example : load32 (traversal machine).core.memory 0x2b9a8=0x7fffd := by decide +kernel
example : (traversal machine).core.regs 4=0xfffffff5 := by decide +kernel
example : load32 (traversal machine).core.memory 0xfffffffd=0x2b760 := by decide +kernel
example : load32 (traversal machine).core.memory 0xfffffff9=3 := by decide +kernel
example : load32 (traversal machine).core.memory 0xfffffff5=0x2bbff := by decide +kernel
example : load32 (traversal machine).core.memory 0x2c1e4=0xffff6000 := by decide +kernel
example : load32 (traversal machine).core.memory 0x2c1e8=0xa000 := by decide +kernel
end AimSetupFixture

import Doom.Proofs.E1M1PathInit
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace PathInitFixture
open OriginalPathInit
def ox : Fixed := ⟨0⟩
def oy : Fixed := ⟨0⟩
def sx : Fixed := ⟨-8388608⟩
def sy : Fixed := ⟨0⟩
def ex : Fixed := ⟨8388608⟩
def ey : Fixed := ⟨-16777216⟩
def machine : X86Memory.State :=
  {regs := fun r => if r=0 then sx.raw.toBitVec else if r=2 then sy.raw.toBitVec
    else if r=3 then ex.raw.toBitVec else if r=1 then ey.raw.toBitVec
    else if r=4 then 1 else 0x12345678,
   memory := store32 (store32 (fun _ => 0) 0x13580 0xffffffff) 5 7}
-- A diagnostic boundary state, not asserted reachable from E1M1 initialization.
theorem inputs : Inputs machine ox oy sx sy ex ey := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change ∀ (a : Word), a ∈ [0x2c104,0x2c108,5] → ∀ (b : Word),
      b ∈ [0xfffffffd,0xfffffff9,0xfffffff5,0x2c028,0x2c024,0x13580,
        0x2ba18,0x2ba10,0x2ba14,0x2ba1c,0xffffffd1,0xffffffd5,0xffffffd9,0xffffffcd,0xffffffdd] → Apart a b
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_imp,
      forall_eq_or_imp,forall_eq,forall_and]
    repeat' constructor
    all_goals unfold Apart
    all_goals decide +kernel
  · unfold Separated Apart
    decide +kernel

example : Ready machine (result machine) (Collision.pathStart ox oy sx sy ex ey) := ready _ _ _ _ _ _ _ inputs
example : load32 (result machine).core.memory 0x2ba10=0xff810000 := by decide +kernel
example : load32 (result machine).core.memory 0x2ba14=0x10000 := by decide +kernel
example : load32 (result machine).core.memory 0xffffffd1=0xffffffff := by decide +kernel
example : load32 (result machine).core.memory 0xffffffdd=0xfffffffe := by decide +kernel
example : load32 (result machine).core.memory 0xffffffcd=512 := by decide +kernel
example : load32 (result machine).core.memory 0x13580=0 := by decide +kernel
example : load32 (result machine).core.memory 0x2c024=4 := by decide +kernel
example : (result machine).core.regs 4=0xffffffc5 := by decide +kernel

def quadrant (i : Fin 4) : X86Memory.State :=
  {machine with regs := write (write machine.regs 0 (sx.raw.toBitVec+BitVec.ofNat 32 (i.val%2))) 2 (BitVec.ofNat 32 (i.val/2))}
example : ∀ i : Fin 4,
    load32 (result (quadrant i)).core.memory 0x2ba10=(if i.val%2=0 then 0xff810000 else 0xff800001) ∧
    load32 (result (quadrant i)).core.memory 0x2ba14=(if i.val/2=0 then 0x10000 else 1) := by decide +kernel
end PathInitFixture

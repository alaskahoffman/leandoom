import Doom.Verification.X86Block
import Doom.Proofs.OriginalMul
import Std.Tactic.BVDecide

namespace Doom.Proofs.BlockSummary
open Verification X86 X86Memory X86Block

/-- Arithmetic summary shared by every inlined original FixedMul block. -/
def mulWord (a b : Word) : Word :=
  (Fixed.mul ⟨Int32.ofBitVec a⟩ ⟨Int32.ofBitVec b⟩).raw.toBitVec

def multiply (s : State) : State :=
  { s with regs := (write (write s.regs eax (mulWord (s.regs eax) (s.regs ebx))) edx
    ((BitVec.ofInt 64 ((s.regs eax).toInt * (s.regs ebx).toInt)).extractLsb' 32 32)) }

/-- Reuses the original multiplication theorem instead of re-proving arithmetic. -/
theorem multiply_correct (s : State) :
    X86Block.execute (.arithmetic (.shrd eax edx 16))
      (X86Block.execute (.arithmetic (.imul ebx)) s) = multiply s := by
  have h := original_mul_result s.regs
  change some _ = some (mulWord (s.regs eax) (s.regs ebx)) at h
  have h := Option.some.inj h
  change State.mk _ s.memory = State.mk _ s.memory
  congr 1
  funext r
  by_cases ha : r = eax
  · subst r; exact h
  · simp [X86Block.execute, X86.execute, write, ha]

/-- A small proof-producing simplifier for decoded blocks. Recognized FixedMul
pairs use their existing theorem; everything else retains instruction semantics.
This is an extensible summary library, not a new trusted execution engine. -/
def summarized : List X86Block.Op → State → State
  | .arithmetic (.imul 3) :: .arithmetic (.shrd 0 2 16) :: ops, s =>
      summarized ops (multiply s)
  | op :: ops, s => summarized ops (X86Block.execute op s)
  | [], s => s

theorem summarized_correct (ops : List X86Block.Op) (s : State) :
    eval ops s = summarized ops s := by
  fun_induction summarized ops s with
  | case1 ops s ih => simpa only [eval, multiply_correct] using ih
  | case2 op ops s _ ih => exact ih
  | case3 s => rfl

/-- Generic entry point: decode original bytes, reuse available summaries, then
normalize loads, stores and register assignments to an explicit state function. -/
theorem certified (code : List UInt8) (ops : List X86Block.Op) (n : Nat)
    (decoded : decodeBlock n code = some ops) (s : State) :
    X86Block.run n code s = some (summarized ops s) :=
  of_decoded_summary code ops n (summarized ops) decoded (summarized_correct ops) s

theorem load_store (m : Memory) (a v : Word) : load32 (store32 m a v) a = v := by
  simp only [load32, store32]
  bv_decide

/-- Disjointness of byte ranges, including wrapping addresses. -/
def Apart (a b : Word) : Prop :=
  ∀ i j : Fin 4, a + BitVec.ofNat 32 i.val ≠ b + BitVec.ofNat 32 j.val

theorem load_store_apart (m : Memory) (a b v : Word) (h : Apart b a) :
    load32 (store32 m a v) b = load32 m b := by
  have h00 : b + 0 ≠ a + 0 := h 0 0
  have h01 : b + 0 ≠ a + 1 := h 0 1
  have h02 : b + 0 ≠ a + 2 := h 0 2
  have h03 : b + 0 ≠ a + 3 := h 0 3
  have h10 : b + 1 ≠ a + 0 := h 1 0
  have h11 : b + 1 ≠ a + 1 := h 1 1
  have h12 : b + 1 ≠ a + 2 := h 1 2
  have h13 : b + 1 ≠ a + 3 := h 1 3
  have h20 : b + 2 ≠ a + 0 := h 2 0
  have h21 : b + 2 ≠ a + 1 := h 2 1
  have h22 : b + 2 ≠ a + 2 := h 2 2
  have h23 : b + 2 ≠ a + 3 := h 2 3
  have h30 : b + 3 ≠ a + 0 := h 3 0
  have h31 : b + 3 ≠ a + 1 := h 3 1
  have h32 : b + 3 ≠ a + 2 := h 3 2
  have h33 : b + 3 ≠ a + 3 := h 3 3
  simp_all [load32, store32]

/-- Reduce only the closed decoder output, then symbolically execute it with
proved summaries. Avoid reducing the symbolic game state or concrete tables. -/
macro "summarize_x86 " ops:term : tactic => `(tactic| (
  conv => lhs; pattern ($ops); reduce
  simp [summarized, X86Block.execute, X86Memory.execute, Address.eval, put,
    multiply, write, eax, ebx, edx, BitVec.add_assoc] <;> rfl))

end Doom.Proofs.BlockSummary

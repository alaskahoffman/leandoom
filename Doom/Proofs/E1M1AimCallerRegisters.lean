import Doom.Proofs.E1M1AimPreRayQuery
import Doom.Proofs.DeathStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimCallerRegisters
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context)
open E1M1PathMapQuery (traversal withStack)
attribute [local irreducible] load32 store32

/-- Only the later setup stores must avoid the four freshly saved words. -/
def SavedSafe (s : X86Memory.State) : Prop :=
  ∀ off∈[(16#32),12,8,4], ∀ b∈(OriginalAimSetup.writes (withStack s (s.regs 4-(16#32)))).toList,
    Apart (s.regs 4-off) b

/-- The four actual pushes encode the original EBP, EDI, ESI and ECX. Slot
separation holds even when 32-bit stack subtraction wraps. -/
theorem saved (s : X86Memory.State) :
    load32 (OriginalAimQuery.saved s).memory (s.regs 4-16)=s.regs 5 ∧
    load32 (OriginalAimQuery.saved s).memory (s.regs 4-12)=s.regs 7 ∧
    load32 (OriginalAimQuery.saved s).memory (s.regs 4-8)=s.regs 6 ∧
    load32 (OriginalAimQuery.saved s).memory (s.regs 4-4)=s.regs 1 := by
  have memory : (OriginalAimQuery.saved s).memory=
      store32 (store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 1))
        (s.regs 4-8) (s.regs 6)) (s.regs 4-12) (s.regs 7)) (s.regs 4-16) (s.regs 5) := by
    simp [OriginalAimQuery.saved,X86Routine.pushWord,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [memory]
  have apart (a b : Fin 32) (h : a≠b) := DeathStack.slots_apart (s.regs 4) a b h
  refine ⟨load_store _ _ _,?_,?_,?_⟩
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-12) (s.regs 4-16) from apart 3 4 (by decide))]
    exact load_store _ _ _
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-16) from apart 2 4 (by decide)),load_store_apart _ _ _ _ (show Apart (s.regs 4-8) (s.regs 4-12) from apart 2 3 (by decide))]
    exact load_store _ _ _
  · rw [load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-16) from apart 1 4 (by decide)),load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-12) from apart 1 3 (by decide)),
      load_store_apart _ _ _ _ (show Apart (s.regs 4-4) (s.regs 4-8) from apart 1 2 (by decide))]
    exact load_store _ _ _

/-- Preserve the newly saved values through aim setup, rather than assuming
the contents of stack slots at traversal entry. -/
theorem setup_saved (s : X86Memory.State) (safe : SavedSafe s) :
    load32 (traversal s).core.memory (s.regs 4-16)=s.regs 5 ∧
    load32 (traversal s).core.memory (s.regs 4-12)=s.regs 7 ∧
    load32 (traversal s).core.memory (s.regs 4-8)=s.regs 6 ∧
    load32 (traversal s).core.memory (s.regs 4-4)=s.regs 1 := by
  have keep (off : Word) (member : off∈[(16#32),12,8,4]) :
      load32 (traversal s).core.memory (s.regs 4-off)=
        load32 (OriginalAimQuery.saved s).memory (s.regs 4-off) := by
    apply OriginalAimSetup.frame9
    simpa only [OriginalAimSetup.writes,E1M1PathMapQuery.ray_stack,withStack,write,ite_true] using safe off member
  rw [keep _ (by simp),keep _ (by simp),keep _ (by simp),keep _ (by simp)]
  exact saved s

/-- What P_AimLineAttack restores to its original caller. No EBX/EDX or flags
preservation is claimed. -/
structure Restores (s : X86Memory.State) (out : X86Control.State) : Prop where
  stack : out.core.regs 4=s.regs 4+4
  pc : out.pc=(load32 s.memory (s.regs 4)).toNat
  bp : out.core.regs 5=s.regs 5
  di : out.core.regs 7=s.regs 7
  si : out.core.regs 6=s.regs 6
  cx : out.core.regs 1=s.regs 1

/-- Rebase the full query's proved restoration to pre-ray register values and
its original return word. All separation conditions refer to initial addresses. -/
theorem restores (q : Context) (s : X86Memory.State) (out : X86Control.State)
    (stack : s.regs 4=q.sp-24) (safe : SavedSafe s)
    (returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))
    (returned : E1M1AimSavedCaller.Restores (traversal s) (q.sp-136) out) : Restores s out := by
  obtain ⟨sp,pc,bp,di,si,cx⟩ := returned
  obtain ⟨bp0,di0,si0,cx0⟩ := setup_saved s safe
  have offsets : (q.sp-136+96,q.sp-136+100,q.sp-136+104,q.sp-136+108)=
      (s.regs 4-16,s.regs 4-12,s.regs 4-8,s.regs 4-4) := by
    rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have a := congrArg Prod.fst offsets
  have b := congrArg (fun t => t.2.1) offsets
  have c := congrArg (fun t => t.2.2.1) offsets
  have d := congrArg (fun t => t.2.2.2) offsets
  simp only [Prod.fst,Prod.snd] at a b c d
  rw [a] at bp; rw [b] at di; rw [c] at si; rw [d] at cx
  refine ⟨sp.trans ?_,pc.trans (congrArg BitVec.toNat (E1M1AimSetupCatalog.return_address q s stack returnSafe)),
    bp.trans bp0,di.trans di0,si.trans si0,cx.trans cx0⟩
  rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
end Doom.Proofs.E1M1AimCallerRegisters

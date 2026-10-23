import Doom.Proofs.E1M1CellWalkLimit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1OutsideLine
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant
attribute [local irreducible] load32

def result (s : X86Control.State) := E1M1PathMapCaller.returned s.core

/-- Both bounds branches have only the real CALL/PUSH/local stores. -/
theorem memory (s : X86Control.State) :
    (result s).core.memory=(OriginalLineBounds.entry (E1M1PathMapCaller.call s.core).core).memory := by
  unfold result E1M1PathMapCaller.returned OriginalLineBounds.result
  split
  · exact (OriginalLineBounds.guard_frame _).1
  · exact (OriginalLineBounds.guard_frame _).1

theorem read_word (s : X86Control.State) (sp a : Word) (stack : s.core.regs 4=sp-(112#32))
    (safe : CallerSafe sp a) : load32 (result s).core.memory a=load32 s.core.memory a := by
  rw [memory]
  have h := E1M1CellWalkInvariant.caller_safe s.core sp a stack safe
  have k := E1M1PathMapCaller.safe_at_call s.core a h
  exact (OriginalLineBounds.entry_frame _ a k.1 k.2).trans (E1M1PathMapCaller.call_frame s.core a h.1)

/-- All live grid registers survive the outside return, including saved EDI. -/
theorem register (s : X86Control.State)
    (outside : ¬OriginalLineBounds.Inside (OriginalLineBounds.entry (E1M1PathMapCaller.call s.core).core))
    (reg : Fin 8) (member : reg∈([1,5,6,7] : List (Fin 8))) :
    (result s).core.regs reg=s.core.regs reg := by
  have guardReg (t : X86Memory.State) (i : Fin 8) (ne : i≠3) :
      (OriginalLineBounds.guarded t).core.regs i=t.regs i := by
    unfold OriginalLineBounds.guarded
    split <;> (try split) <;> (try split) <;> simp [OriginalLineBounds.loaded,put,write,ne]
  have guardSP := (OriginalLineBounds.guard_frame (OriginalLineBounds.entry (E1M1PathMapCaller.call s.core).core)).2
  have guardMem := (OriginalLineBounds.guard_frame (OriginalLineBounds.entry (E1M1PathMapCaller.call s.core).core)).1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  all_goals simp [result,E1M1PathMapCaller.returned,OriginalLineBounds.result,if_neg outside,
    OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,OriginalLineBounds.r1,put,write]
  all_goals try { rw [guardReg _ _ (by decide)]; rfl }
  rw [guardSP,guardMem]
  let t := (E1M1PathMapCaller.call s.core).core
  change load32 (OriginalLineBounds.entry t).memory ((OriginalLineBounds.entry t).regs 4+4)=s.core.regs 7
  have apart : Apart (t.regs 4-4) (t.regs 4-8) := by
    simpa [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (t.regs 4) (-4) (-8) (by unfold Apart; decide)
  simp only [OriginalLineBounds.entry,OriginalLineBounds.e2,OriginalLineBounds.e1,X86Routine.pushWord,put,write]
  have addr : t.regs 4-8+4=t.regs 4-4 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  simp only [ite_true]
  rw [addr,load_store_apart _ _ _ _ apart]
  change load32 (store32 t.memory (t.regs 4-4) (t.regs 7)) (t.regs 4-4)=s.core.regs 7
  rw [load_store]
  rfl

/-- Out-of-map line iteration returns to its actual caller with no callback.
The numeric observation is unchanged, and protected words retain their values. -/
theorem execution (q : Context) (s : X86Control.State) (x y : Int32)
    (common : Common q)
    (stack : s.core.regs 4=q.sp-(112#32))
    (maps : E1M1CellMapInvariant.Image s.core.memory q.sp q.base q.lines q.words q.width q.height)
    (pc : s.pc=0x2ca7f) (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (outMap : Collision.pathCellInside x y q.width q.height=false) :
    let out := result s
    (∃ n≤22, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.pc=0x2ca94 ∧ out.core.regs 0=(1#32) ∧ out.core.regs 4=q.sp-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core ∧
    E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory := by
  have facts := E1M1CellMapInvariant.inputs s.core q.sp q.base q.lines q.words q.width q.height stack maps common.mapLayout
  have encoding := E1M1PathMapCaller.bounds_inputs s.core x y q.width q.height facts.1 mapX mapY
  have outside : ¬OriginalLineBounds.Inside (OriginalLineBounds.entry (E1M1PathMapCaller.call s.core).core) := by
    rw [OriginalLineBounds.live_bounds _ _ _ _ _ encoding,outMap]; decide
  obtain ⟨⟨m,hm,run⟩,value,sp,ret⟩ := E1M1PathMapBounds.outside_returns _ _ x y q.width q.height encoding outMap
  obtain ⟨n,hn,call⟩ := E1M1PathMapCaller.enter_execution s.core s.flags
    (E1M1CellMapInvariant.enabled s.core q.sp q.base q.lines q.words q.width q.height stack maps true)
  rw [OriginalPathXStep.at_pc _ _ pc] at call
  have callPC : (E1M1PathMapCaller.call s.core).pc=0x2c520 := rfl
  rw [OriginalPathXStep.at_pc _ _ callPC] at run
  change (result s).pc=_ at ret
  change (result s).core.regs 4=_ at sp
  have stop : (result s).pc=0x2ca94 := by
    rw [ret,E1M1PathMapCaller.call_stack,E1M1PathMapCaller.call_return]; rfl
  have outStack : (result s).core.regs 4=q.sp-(112#32) := by
    rw [sp,E1M1PathMapCaller.call_stack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans
    (X86CodeMemory.lift_success (call.transfer _ [] E1M1NextCellScan.contains_caller (by simp)) FloorCaller.cm)
    (X86CodeMemory.lift_success (run.transfer _ [] (fun p hp =>
      (E1M1NextCellScan.contains_caller p (by rw [E1M1PathMapCaller.contains_bounds p hp]; exact hp)).trans
      (E1M1PathMapCaller.contains_bounds p hp)) (by simp)) FloorCaller.cm)⟩,
    stop,value,outStack,?_,fun a safe => read_word s q.sp a stack safe.caller⟩
  apply E1M1FiringGridState.transport
  · exact register s outside
  · intro off member
    change load32 (result s).core.memory ((result s).core.regs 4+off)=load32 s.core.memory (s.core.regs 4+off)
    rw [outStack,stack]
    apply read_word s q.sp _ stack
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl
    · exact E1M1GridLocals.below q.sp off member ⟨0,by decide⟩
    · exact E1M1GridLocals.below q.sp off member ⟨1,by decide⟩
    · exact E1M1GridLocals.below q.sp off member ⟨2,by decide⟩
end Doom.Proofs.E1M1OutsideLine

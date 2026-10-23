import Doom.Proofs.E1M1NoiseFootprint
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoisePreservation
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseRecursive E1M1NoiseFootprint
abbrev sector (s : X86Control.State) := E1M1NoiseAlert.sectorResult s.core
abbrev dispatch (s : X86Control.State) := E1M1NoiseIteration.dispatched s.core
abbrev advance (s : X86Control.State) := NoiseTraversal.advanced s.core
abbrev finish (s : X86Control.State) := NoiseTraversal.returned s.core
abbrev startLines (s : X86Control.State) := NoiseTraversal.initialized (sector s).core

/-- A finite derivation of the existing evaluator, carrying conservative write
addresses. No constructor assumes memory preservation or callee behavior. -/
inductive Trace : Phase → X86Control.State → X86Control.State → List Word → Prop
  | sectorDone (s) (done : (sector s).pc=0x27011) :
      Trace .sector s (finish (sector s)) (sectorWrites s.core)
  | sectorMore (s t w) (more : (sector s).pc=0x26fa6)
      (body : Trace .lines (startLines s) t w) :
      Trace .sector s t (sectorWrites s.core++w)
  | lineDone (s) (opening : OpeningReturns s.core) (skip : (dispatch s).pc=0x27006)
      (done : (advance (dispatch s)).pc=0x27011) :
      Trace .lines s (finish (advance (dispatch s))) (lineWrites s.core)
  | lineMore (s t w) (opening : OpeningReturns s.core) (skip : (dispatch s).pc=0x27006)
      (more : (advance (dispatch s)).pc=0x26fa8)
      (body : Trace .lines (advance (dispatch s)) t w) :
      Trace .lines s t (lineWrites s.core++w)
  | childDone (s u w) (opening : OpeningReturns s.core) (call : (dispatch s).pc=0x26f60)
      (child : Trace .sector (dispatch s) u w) (ret : u.pc=0x27006)
      (done : (advance u).pc=0x27011) :
      Trace .lines s (finish (advance u)) (lineWrites s.core++w)
  | childMore (s u t w v) (opening : OpeningReturns s.core) (call : (dispatch s).pc=0x26f60)
      (child : Trace .sector (dispatch s) u w) (ret : u.pc=0x27006)
      (more : (advance u).pc=0x26fa8) (body : Trace .lines (advance u) t v) :
      Trace .lines s t (lineWrites s.core++w++v)

/-- Computable conservative footprint. Failed evaluations also have a footprint,
which carries no execution claim. Each successful trace is tied to this list. -/
def writes : Nat → Phase → X86Control.State → List Word
  | 0,_,_ => []
  | k+1,.sector,s =>
    if (sector s).pc=0x27011 then sectorWrites s.core
    else sectorWrites s.core++writes k .lines (startLines s)
  | k+1,.lines,s =>
    let d := dispatch s
    if d.pc=0x26f60 then
      match eval k .sector d with
      | none => lineWrites s.core
      | some u => lineWrites s.core++writes k .sector d++
          (if (advance u).pc=0x26fa8 then writes k .lines (advance u) else [])
    else lineWrites s.core++
      (if (advance d).pc=0x26fa8 then writes k .lines (advance d) else [])

/-- Every successful evaluation supplies a derivation, including all nested
children and the remaining parent lines. -/
theorem of_eval (k : Nat) (phase : Phase) (s t : X86Control.State)
    (h : eval k phase s=some t) : Trace phase s t (writes k phase s) := by
  induction k generalizing phase s t with
  | zero => simp [eval] at h
  | succ k ih =>
    cases phase with
    | sector =>
      simp only [eval] at h
      split at h
      · rename_i done
        cases Option.some.inj h
        simpa only [writes,sector,done,ite_true] using Trace.sectorDone s done
      · split at h
        · rename_i more
          have body := ih .lines _ _ h
          simpa only [writes,sector,if_neg (by omega : (E1M1NoiseAlert.sectorResult s.core).pc≠0x27011)] using Trace.sectorMore s t _ more body
        · contradiction
    | lines =>
      simp only [eval] at h
      split at h
      · contradiction
      · rename_i opening
        have opening : OpeningReturns s.core := Classical.not_not.mp opening
        split at h
        · rename_i call
          simp only [Option.bind_eq_bind] at h
          cases childRun : eval k .sector (dispatch s) with
          | none => simp only [dispatch] at childRun; simp [childRun] at h
          | some u =>
            simp only [dispatch] at childRun
            simp only [childRun,Option.bind_some] at h
            split at h
            · rename_i ret
              have child := ih .sector _ _ childRun
              split at h
              · rename_i more
                have body := ih .lines _ _ h
                simpa only [writes,dispatch,call,ite_true,childRun,advance,more] using Trace.childMore s u t _ _ opening call child ret more body
              · split at h
                · rename_i done
                  cases Option.some.inj h
                  have stop : (advance u).pc≠0x26fa8 := by change (NoiseTraversal.advanced u.core).pc≠0x26fa8; omega
                  simpa only [writes,dispatch,call,ite_true,childRun,if_neg stop,List.append_nil] using Trace.childDone s u _ opening call child ret done
                · contradiction
            · simp at h
        · split at h
          · rename_i skip
            simp only [Option.bind_eq_bind,Option.bind_some] at h
            split at h
            · rename_i more
              have body := ih .lines _ _ h
              simpa only [writes,dispatch,skip,show (0x27006 : Nat)≠0x26f60 by decide,ite_false,advance,more,ite_true] using Trace.lineMore s t _ opening skip more body
            · split at h
              · rename_i done
                cases Option.some.inj h
                have stop : (advance (dispatch s)).pc≠0x26fa8 := by change (NoiseTraversal.advanced (E1M1NoiseIteration.dispatched s.core).core).pc≠0x26fa8; omega
                simpa only [writes,if_neg (by change (E1M1NoiseIteration.dispatched s.core).pc≠0x26f60; omega),if_neg stop,List.append_nil] using Trace.lineDone s opening skip done
              · contradiction
          · simp at h

@[simp] theorem finish_memory (s : X86Control.State) : (finish s).core.memory=s.core.memory := rfl
@[simp] theorem advance_memory (s : X86Control.State) : (advance s).core.memory=s.core.memory := rfl
@[simp] theorem start_memory (s : X86Control.State) : (startLines s).core.memory=(sector s).core.memory := rfl
@[simp] theorem advance_sp (s : X86Control.State) : (advance s).core.regs 4=s.core.regs 4 := by
  simp [advance,NoiseTraversal.advanced,put,write]
@[simp] theorem start_sp (s : X86Control.State) : (startLines s).core.regs 4=s.core.regs 4-(24#32) := by
  simp [startLines,NoiseTraversal.initialized,put,write]

theorem Trace.frame {phase s t w} (h : Trace phase s t w) : PlayerHeight.Frame s.core.memory t.core.memory w := by
  induction h with
  | sectorDone s _ => exact sector_frame s.core
  | sectorMore s t w _ _ ih => exact frame_trans (sector_frame s.core) ih
  | lineDone s _ _ _ => exact dispatch_frame s.core
  | lineMore s t w _ _ _ _ ih => exact frame_trans (dispatch_frame s.core) ih
  | childDone s u w _ _ _ _ _ ih => exact frame_trans (dispatch_frame s.core) ih
  | childMore s u t w v _ _ _ _ _ _ child body => exact frame_trans (frame_trans (dispatch_frame s.core) child) body

/-- Return values read from the final memory at the invocation's own stack
base. This statement is unconditional: an overlapping write may corrupt them. -/
structure ReturnView (sp : Word) (t : X86Control.State) : Prop where
  stack : t.core.regs 4=sp+(28#32)
  pc : t.pc=(load32 t.core.memory (sp+(24#32))).toNat
  bp : t.core.regs 5=load32 t.core.memory (sp+(4#32))
  di : t.core.regs 7=load32 t.core.memory (sp+(8#32))
  si : t.core.regs 6=load32 t.core.memory (sp+(12#32))
  c : t.core.regs 1=load32 t.core.memory (sp+(16#32))
  b : t.core.regs 3=load32 t.core.memory (sp+(20#32))

def base (phase : Phase) (s : X86Control.State) : Word :=
  match phase with | .sector => s.core.regs 4-(24#32) | .lines => s.core.regs 4

theorem finish_view (s : X86Control.State) : ReturnView (s.core.regs 4) (finish s) := by
  constructor <;> simp [finish,NoiseTraversal.returned,NoiseTraversal.restored,PspriteLoop.popped,put,write,BitVec.add_assoc]

private theorem skip_sp (s : X86Control.State) (skip : (dispatch s).pc=0x27006) :
    (dispatch s).core.regs 4=s.core.regs 4 := by
  rw [dispatch,dispatch_sp]
  simp only [dispatch] at skip
  rw [skip]; rfl
private theorem child_sp (s u : X86Control.State) (call : (dispatch s).pc=0x26f60)
    (view : ReturnView (base .sector (dispatch s)) u) : u.core.regs 4=s.core.regs 4 := by
  rw [view.stack]
  simp only [base,dispatch,dispatch_sp]
  simp only [dispatch] at call
  simp [call,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem Trace.view {phase s t w} (h : Trace phase s t w) : ReturnView (base phase s) t := by
  induction h with
  | sectorDone s _ => simpa [base,sector] using finish_view (sector s)
  | sectorMore s t w _ _ ih => simpa only [base,start_sp] using ih
  | lineDone s _ skip _ => simpa only [base,advance_sp,skip_sp s skip] using finish_view (advance (dispatch s))
  | lineMore s t w _ skip _ _ ih => simpa only [base,advance_sp,skip_sp s skip] using ih
  | childDone s u w _ call _ _ _ ih => simpa only [base,advance_sp,child_sp s u call ih] using finish_view (advance u)
  | childMore s u t w v _ call _ _ _ _ child body => simpa only [base,advance_sp,child_sp s u call child] using body

/-- The six words protected by this invocation's frame. -/
def SafeWords (entry : X86Memory.State) (w : List Word) : Prop :=
  ∀ a, a ∈ E1M1NoiseFrame.slots entry → ∀ b, b ∈ w → Apart a b

structure Restored (entry : X86Memory.State) (t : X86Control.State) : Prop where
  stack : t.core.regs 4=entry.regs 4+(4#32)
  pc : t.pc=(load32 entry.memory (entry.regs 4)).toNat
  bp : t.core.regs 5=entry.regs 5
  di : t.core.regs 7=entry.regs 7
  si : t.core.regs 6=entry.regs 6
  c : t.core.regs 1=entry.regs 1
  b : t.core.regs 3=entry.regs 3

private theorem restore_view (entry s : X86Memory.State) (t : X86Control.State)
    (saved : E1M1NoiseFrame.Saved entry s) (view : ReturnView (s.regs 4) t)
    (words : ∀ a, a ∈ E1M1NoiseFrame.slots entry → load32 t.core.memory a=load32 s.memory a) :
    Restored entry t := by
  obtain ⟨ret,b,c,si,di,bp⟩ := E1M1NoiseFrame.saved_words entry
  have read (a : Word) (ha : a ∈ E1M1NoiseFrame.slots entry) := (words a ha).trans (saved.words a ha)
  have ret := (read _ (by simp [E1M1NoiseFrame.slots])).trans ret
  have b := (read _ (by simp [E1M1NoiseFrame.slots])).trans b
  have c := (read _ (by simp [E1M1NoiseFrame.slots])).trans c
  have si := (read _ (by simp [E1M1NoiseFrame.slots])).trans si
  have di := (read _ (by simp [E1M1NoiseFrame.slots])).trans di
  have bp := (read _ (by simp [E1M1NoiseFrame.slots])).trans bp
  simp [BitVec.sub_eq_add_neg] at ret b c si di bp
  constructor
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] using view.stack
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,ret] using view.pc
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,bp] using view.bp
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,di] using view.di
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,si] using view.si
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,c] using view.c
  · simpa [saved.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,b] using view.b

theorem Trace.restores_lines {s t w} (h : Trace .lines s t w) (entry : X86Memory.State)
    (saved : E1M1NoiseFrame.Saved entry s.core) (safe : SafeWords entry w) : Restored entry t :=
  restore_view entry s.core t saved h.view (fun a ha => h.frame a (safe a ha))

/-- Drop only this invocation's five prologue stores. Later writes to the same
addresses remain in the list, so aliasing cannot be hidden by filtering. -/
def SectorSafe (entry : X86Memory.State) (w : List Word) : Prop := SafeWords entry (w.drop 5)

theorem Trace.restores_sector {s t w} (h : Trace .sector s t w)
    (safe : SectorSafe s.core w) : Restored s.core t := by
  cases h with
  | sectorDone s done =>
    have sep : E1M1NoiseFrame.SectorSafe s.core := safe
    have saved := E1M1NoiseFrame.sector_saved s.core sep
    exact restore_view s.core (sector s).core (finish (sector s)) saved (finish_view _) (fun _ _ => rfl)
  | sectorMore s t w more body =>
    have sep : E1M1NoiseFrame.SectorSafe s.core := by
      intro a ha b hb
      exact safe a ha b (by simpa [sectorWrites] using List.mem_append_left w hb)
    have bodySafe : SafeWords s.core w := by
      intro a ha b hb
      exact safe a ha b (by simpa [sectorWrites] using (List.mem_append_right [s.core.regs 0+(66#32),s.core.regs 0+(18#32),s.core.regs 0+(22#32)] hb))
    have saved := E1M1NoiseFrame.sector_saved s.core sep
    have started : E1M1NoiseFrame.Saved s.core (startLines s).core :=
      ⟨by simpa [startLines,NoiseTraversal.initialized,put,write] using saved.sp,saved.words⟩
    exact body.restores_lines s.core started bodySafe

/-- No per-child restoration or return-address hypotheses: protection of the
computed write footprint suffices at every admitted nesting depth. -/
theorem eval_restores (k : Nat) (s t : X86Control.State)
    (run : eval k .sector s=some t) (safe : SectorSafe s.core (writes k .sector s)) : Restored s.core t :=
  (of_eval k .sector s t run).restores_sector safe

theorem eval_frame (k : Nat) (phase : Phase) (s t : X86Control.State)
    (run : eval k phase s=some t) : PlayerHeight.Frame s.core.memory t.core.memory (writes k phase s) :=
  (of_eval k phase s t run).frame

/-- Connect arbitrary recursive children to the parent's nonwrapping line
measure. Completion and address separation remain explicit; termination is not
assumed or obtained merely from this local progress result. -/
theorem child_remaining (k : Nat) (parent : X86Memory.State) (f : Option Flags) (t : X86Control.State) (n : Nat)
    (run : eval k .sector (NoiseTraversal.recursiveCall parent f)=some t)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core
      (writes k .sector (NoiseTraversal.recursiveCall parent f)))
    (index : (parent.regs 6).toNat<n) (small : n≤2147483647) :
    n-((advance t).core.regs 6).toNat < n-(parent.regs 6).toNat := by
  have restore := eval_restores k _ t run safe
  have si : t.core.regs 6=parent.regs 6 := by
    simpa [NoiseTraversal.recursiveCall,X86Routine.pushWord,write] using restore.si
  simpa only [si] using E1M1NoiseFrame.remaining_decreases t.core n (by simpa only [si] using index) small

/-- The recursive return check is a consequence of the CALL's saved word and
whole-traversal protection, including children with further children. -/
theorem eval_child_returns (k : Nat) (parent : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (run : eval k .sector (NoiseTraversal.recursiveCall parent f)=some t)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core
      (writes k .sector (NoiseTraversal.recursiveCall parent f))) :
    t.pc=0x27006 ∧ t.core.regs 4=parent.regs 4 ∧ t.core.regs 6=parent.regs 6 ∧ t.core.regs 5=parent.regs 5 := by
  have h := eval_restores k _ t run safe
  have pc := h.pc; have sp := h.stack; have si := h.si; have bp := h.bp
  simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,write,load_store,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] at pc sp si bp
  exact ⟨pc,sp,si,bp⟩

/-- Execute an arbitrary completed recursive child and advance the parent.
Unlike the earlier terminal-child theorem, this has no leaf/pruning restriction
and no assumed child return address. -/
theorem child_execution (k : Nat) (parent : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (run : eval k .sector (NoiseTraversal.recursiveCall parent f)=some t)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core
      (writes k .sector (NoiseTraversal.recursiveCall parent f))) :
    Runs (bound k+5) (NoiseTraversal.recursiveCall parent f) (advance t) := by
  have ret := (eval_child_returns k parent f t run safe).1
  obtain ⟨n,hn,p⟩ := execution k .sector _ t rfl run
  obtain ⟨m,hm,q,_⟩ := X86Routine.run_path (NoiseTraversal.advance_execution t.core t.flags)
  have contains (pc : Nat) (h : NoiseTraversal.program pc≠none) :
      E1M1NoiseOpening.program pc=NoiseTraversal.program pc := by
    have prior := E1M1NoiseTraversal.contains_traversal pc h
    rw [E1M1NoiseOpening.contains_prior pc (by rw [prior]; exact h),prior]
  have q := (X86CodeMemory.lift_success q FloorCaller.cm).transfer E1M1NoiseOpening.program [] contains (by simp)
  have eq : t=⟨t.core,t.flags,0x27006⟩ := by rw [←ret]
  rw [←eq] at q
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
end Doom.Proofs.E1M1NoisePreservation

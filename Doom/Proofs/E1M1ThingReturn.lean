import Doom.Proofs.E1M1ThingFraction
import Doom.Proofs.OriginalThingFinish
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingReturn
open Verification X86 X86Memory X86Control BlockSummary

def program : X86Routine.Program := fun pc =>
  match E1M1ThingFraction.program pc with
  | some op => some op
  | none => OriginalThingFinish.program pc

theorem contains_prior (pc : Nat) (h : E1M1ThingFraction.program pc≠none) :
    program pc=E1M1ThingFraction.program pc := by
  unfold program
  cases eq : E1M1ThingFraction.program pc <;> simp_all

theorem contains_finish (pc : Nat) (h : OriginalThingFinish.program pc≠none) :
    program pc=OriginalThingFinish.program pc := by
  have range : 0x2c7da≤pc ∧ pc<0x2c80f := by
    by_cases r : 0x2c7da≤pc ∧ pc<0x2c80f
    · exact r
    · simp [OriginalThingFinish.program,OriginalThingFinish.bytesProgram,r] at h
  have all : ∀ i : Fin 53, program (0x2c7da+i.val)=OriginalThingFinish.program (0x2c7da+i.val) := by decide
  have eq : 0x2c7da+(pc-0x2c7da)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c7da,by omega⟩

theorem contains_resume (pc : Nat) (h : OriginalThingCallback.listed pc≠none) :
    program pc=OriginalThingCallback.listed pc := by
  fun_cases OriginalThingCallback.listed pc <;> simp_all [OriginalThingCallback.listed] <;> decide

def view (s : X86Memory.State) := E1M1ThingFraction.continueFraction (OriginalThingSecondSide.crossing s)
def finished (s : X86Memory.State) := OriginalThingFinish.result (view s)
def resumed (s : X86Memory.State) := OriginalThingCallback.resumed (finished s).core

theorem fraction_regs (s : X86Memory.State) :
    (OriginalThingFraction.result s).core.regs 4=s.regs 4 ∧
    (OriginalThingFraction.result s).core.regs 1=s.regs 1 := by
  unfold OriginalThingFraction.result OriginalThingFraction.tested
  split <;> simp [put,write,(OriginalThingFraction.returned s).2.1,(OriginalThingFraction.returned s).2.2]

theorem view_regs (s : X86Memory.State) : (view s).core.regs 4=s.regs 4 ∧ (view s).core.regs 1=s.regs 1 := by
  unfold view E1M1ThingFraction.continueFraction
  split
  · have r := fraction_regs (OriginalThingSecondSide.crossing s).core
    have old := OriginalThingFractionInputs.crossing_regs s
    exact ⟨r.1.trans old.1,r.2.trans old.2⟩
  · exact OriginalThingFractionInputs.crossing_regs s

/-- Callback saves lie above all endpoint, local-divline and helper scratch writes. -/
theorem view_saved (s : X86Memory.State) (off : Word) (ho : off∈[(24#32),28,32,36,40,44,48]) :
    load32 (view s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  have apart (delta : Word) (hd : delta∈[(0#32),4,8,12,16,20,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40]) :
      Apart (s.regs 4+off) (s.regs 4+delta) := by
    apply OriginalPathXStep.apart_translate
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho hd
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  have down (delta : Word) (hd : delta∈[(4#32),8,12,16,20]) : Apart (s.regs 4+off) (s.regs 4-delta) := by
    rw [BitVec.sub_eq_add_neg]
    apply apart (-delta)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl <;> decide
  have first := OriginalThingFirstSide.frame s (s.regs 4+off) ⟨apart 20 (by simp),down⟩
  have second := OriginalThingSecondSide.frame (OriginalThingFirstSide.result s).core (s.regs 4+off) (by
    rw [(OriginalThingFirstSide.returned s).2.1]
    exact ⟨apart 16 (by simp),down⟩)
  have crossing := second.trans first
  unfold view E1M1ThingFraction.continueFraction
  split
  · apply (OriginalThingFraction.frame (OriginalThingSecondSide.crossing s).core (s.regs 4+off) ?_).trans crossing
    rw [(OriginalThingFractionInputs.crossing_regs s).1]
    intro delta hd
    apply apart delta
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd ⊢
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · exact crossing

def ReturnSafe (s : X86Memory.State) : Prop :=
  ∀ off∈[(36#32),48], ∀ w∈[OriginalThingFinish.cursor (view s).core,
    OriginalThingFinish.cursor (view s).core+(4#32),OriginalThingFinish.cursor (view s).core+(8#32),(0x2c028#32)],
    Apart (s.regs 4+off) w

theorem returned (s : X86Memory.State) (safe : ReturnSafe s) :
    (finished s).pc=(load32 s.memory (s.regs 4+(48#32))).toNat ∧
    (finished s).core.regs 2=load32 s.memory (s.regs 4+(36#32)) ∧
    (finished s).core.regs 4=s.regs 4+(52#32) := by
  have saved (off : Word) (ho : off∈[(36#32),48]) :
      load32 (finished s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
    apply (OriginalThingFinish.frame (view s) _ (safe off ho)).trans
    apply view_saved
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl <;> simp
  exact ⟨(OriginalThingFinish.result_pc (view s)).trans (by rw [(view_regs s).1]; exact congrArg BitVec.toNat (saved (48#32) (by simp))),
    (OriginalThingFinish.result_cursor (view s)).trans (by rw [(view_regs s).1]; exact saved (36#32) (by simp)),
    (OriginalThingFinish.result_sp (view s)).trans (by rw [(view_regs s).1])⟩

theorem outcome_finish (s : X86Control.State) (trace : Collision.Divline) (target : Collision.SolidThing)
    (h : E1M1ThingFraction.Outcome s trace target) :
    s.pc∈[0x2c7da,0x2c7e4,0x2c805] ∧ (OriginalThingFinish.result s).core.regs 0=(1#32) := by
  obtain ⟨hit,_,pc,value⟩ := h
  cases hit with
  | none =>
    simp only [pc,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · split <;> simp
    · rw [OriginalThingFinish.result_value,value]
      split <;> rfl
  | some frac =>
    exact ⟨by simp [pc],by rw [OriginalThingFinish.result_value,pc]; rfl⟩

theorem execution (s : X86Memory.State) (trace : Collision.Divline) (target : Collision.SolidThing)
    (h : E1M1ThingFraction.Outcome (view s) trace target) (safe : ReturnSafe s)
    (ret : load32 s.memory (s.regs 4+(48#32))=(0x2c5d7#32)) :
    (∃ n≤20, X86Routine.Prefix program [] n (view s) (resumed s)) ∧
    (resumed s).core.memory=(finished s).core.memory ∧
    (resumed s).core.regs 4=s.regs 4+(52#32) ∧
    (resumed s).core.regs 2=load32 (finished s).core.memory
      (load32 s.memory (s.regs 4+(36#32))+(44#32)) ∧
    (resumed s).pc=(if (resumed s).core.regs 2=(0#32) then 0x2c5e2 else 0x2c5d2) := by
  have obs := outcome_finish (view s) trace target h
  obtain ⟨n,hn,a⟩ := OriginalThingFinish.execution (view s) obs.1
  obtain ⟨m,hm,b⟩ := OriginalThingCallback.resume_execution (finished s).core (finished s).flags
  have r := returned s safe
  have pc : (finished s).pc=0x2c5d7 := by rw [r.1,ret]; rfl
  rw [OriginalPathXStep.at_pc _ _ pc] at b
  have contains (pc : Nat) (hp : OriginalThingCallback.program pc≠none) : program pc=OriginalThingCallback.program pc := by
    have range : (0x2c5d2≤pc ∧ pc<0x2c5e2) ∨ (0x2c720≤pc ∧ pc<0x2c72b) := by
      by_cases a : 0x2c5d2≤pc ∧ pc<0x2c5e2
      · exact Or.inl a
      · by_cases b : 0x2c720≤pc ∧ pc<0x2c72b
        · exact Or.inr b
        · simp [OriginalThingCallback.program,OriginalThingCallback.bytesProgram,a,b] at hp
    rcases range with range|range
    · have all : ∀ i : Fin 16, program (0x2c5d2+i.val)=OriginalThingCallback.program (0x2c5d2+i.val) := by decide
      have eq : 0x2c5d2+(pc-0x2c5d2)=pc := by omega
      simpa only [eq] using all ⟨pc-0x2c5d2,by omega⟩
    · have all : ∀ i : Fin 11, program (0x2c720+i.val)=OriginalThingCallback.program (0x2c720+i.val) := by decide
      have eq : 0x2c720+(pc-0x2c720)=pc := by omega
      simpa only [eq] using all ⟨pc-0x2c720,by omega⟩
  have resumedObs := OriginalThingCallback.resumed_observe (finished s).core
  have nonzero : (finished s).core.regs 0≠(0#32) := by change (OriginalThingFinish.result (view s)).core.regs 0≠_; rw [obs.2]; decide
  have next := (resumedObs.2.2.2 nonzero).1
  refine ⟨⟨n+m,by omega,OriginalGroupBounds.prefix_join
    (a.transfer program [] contains_finish (by simp)) (b.transfer program [] contains (by simp))⟩,
    resumedObs.1,resumedObs.2.1.trans r.2.2,?_,?_⟩
  · simpa only [resumed,r.2.1] using next
  · unfold resumed
    rw [(resumedObs.2.2.2 nonzero).2]
    change (if OriginalThingCallback.next (finished s).core=(0#32) then _ else _)=_
    rw [show (OriginalThingCallback.resumed (finished s).core).core.regs 2=OriginalThingCallback.next (finished s).core from next]
end Doom.Proofs.E1M1ThingReturn

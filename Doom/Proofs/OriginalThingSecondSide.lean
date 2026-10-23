import Doom.Proofs.OriginalThingFirstSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalThingSecondSide
open Verification X86 X86Memory X86Control BlockSummary
open OriginalThingDiagonal (points)
def thingSecond : List UInt8 := [0xbb,0x10,0xba,0x2,0x0,0x89,0x44,0x24,0x10,0x89,0xea,0x8b,0x44,0x24,0x14,0xe8,0x3f,0xfa,0xff,0xff,0x3b,0x44,0x24,0x10,0x75,0x7,0xb8,0x1,0x0,0x0,0x0,0xeb,0x57]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c78d≤pc ∧ pc<0x2c7ae then X86Routine.decodeAt bytes (pc-0x2c78d) else none
def localProgram := bytesProgram thingSecond
def listed : X86Routine.Program
  | 0x2c78d => some (.immediate 3 0x2ba10,5)
  | 0x2c792 => some (.control (.block (.store ⟨some 4,none,0,16⟩ 0)),4)
  | 0x2c796 => some (.control (.block (.legacy (.mov 2 5))),2)
  | 0x2c798 => some (.control (.block (.load 0 ⟨some 4,none,0,20⟩)),4)
  | 0x2c79c => some (.call (-1473),5)
  | 0x2c7a1 => some (.control (.cmpMemory 0 ⟨some 4,none,0,16⟩),4)
  | 0x2c7a5 => some (.control (.jumpZero false 7),2)
  | 0x2c7a7 => some (.immediate 0 1,5)
  | 0x2c7ac => some (.jump 87,2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : localProgram pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def program : X86Routine.Program := fun pc =>
  match OriginalThingFirstSide.program pc with
  | some op => some op
  | none => localProgram pc

theorem contains_prior (pc : Nat) (h : OriginalThingFirstSide.program pc≠none) :
    program pc=OriginalThingFirstSide.program pc := by
  unfold program
  cases eq : OriginalThingFirstSide.program pc <;> simp_all

theorem contains_local (pc : Nat) (h : localProgram pc≠none) :
    program pc=localProgram pc := by
  have range : 0x2c78d≤pc ∧ pc<0x2c7ae := by
    by_cases r : 0x2c78d≤pc ∧ pc<0x2c7ae
    · exact r
    · simp [localProgram,bytesProgram,r] at h
  have all : ∀ i : Fin 33, program (0x2c78d+i.val)=localProgram (0x2c78d+i.val) := by decide
  have eq : 0x2c78d+(pc-0x2c78d)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2c78d,by omega⟩

def c1 (s : X86Memory.State) := put s 3 0x2ba10
def c2 (s : X86Memory.State) : X86Memory.State := {c1 s with memory:=store32 s.memory (s.regs 4+(16#32)) (s.regs 0)}
def c3 (s : X86Memory.State) := put (c2 s) 2 (s.regs 5)
def c4 (s : X86Memory.State) := put (c3 s) 0 (load32 (c2 s).memory (s.regs 4+(20#32)))
def called (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (c4 s) 0x2c7a1,f,0x2c1e0⟩

theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 5 ⟨s,f,0x2c78d⟩ (called s f) := by
  have path : X86Routine.Prefix listed [] 5 ⟨s,f,0x2c78d⟩ (called s f) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2c792⟩) (by simp) (by rfl) (by simp [called,c4,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2c796⟩) (by simp) (by rfl) (by simp [called,c4,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨c3 s,f,0x2c798⟩) (by simp) (by rfl) (by simp [called,c4,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨c4 s,f,0x2c79c⟩) (by simp) (by rfl) (by simp [called,c4,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨(called s f).core,f,0x2c1e0⟩) (by simp) (by rfl) (by simp [called,c4,c3,c2,c1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags])
    exact .nil _
  exact (path.transfer localProgram [] decoded (by simp)).transfer program [] contains_local (by simp)

def oldSide (s : X86Memory.State) := load32 s.memory (s.regs 4+(16#32))
def tested (s : X86Memory.State) : X86Control.State :=
  if s.regs 0=oldSide s then ⟨put s 0 1,some (compare32 (s.regs 0) (oldSide s)),0x2c805⟩
  else ⟨s,some (compare32 (s.regs 0) (oldSide s)),0x2c7ae⟩

theorem test_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤4, X86Routine.Prefix program [] n ⟨s,f,0x2c7a1⟩ (tested s) := by
  have path : ∃ n≤4, X86Routine.Prefix listed [] n ⟨s,f,0x2c7a1⟩ (tested s) := by
    by_cases same : s.regs 0=oldSide s
    · refine ⟨4,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (oldSide s)),0x2c7a5⟩) (by simp) (by rfl) (by simp [oldSide,X86Routine.execute,X86Control.execute,X86Block.Address.eval])
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (oldSide s)),0x2c7a7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,same])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 1,some (compare32 (s.regs 0) (oldSide s)),0x2c7ac⟩) (by simp) (by rfl) (by simp [X86Routine.execute])
      apply X86Routine.Prefix.step (middle := tested s) (by simp) (by rfl) (by simp [tested,same,X86Routine.execute])
      exact .nil _
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (compare32 (s.regs 0) (oldSide s)),0x2c7a5⟩) (by simp) (by rfl) (by simp [oldSide,X86Routine.execute,X86Control.execute,X86Block.Address.eval])
      apply X86Routine.Prefix.step (middle := tested s) (by simp) (by rfl) (by simp [tested,same,X86Routine.execute,X86Control.execute,cmp32_zero])
      exact .nil _
  obtain ⟨n,hn,path⟩ := path
  exact ⟨n,hn,(path.transfer localProgram [] decoded (by simp)).transfer program [] contains_local (by simp)⟩

theorem apart (sp a b : Word) (h : Apart a b) : Apart (sp+a) (sp+b) := OriginalPathXStep.apart_translate sp a b h

theorem call_observe (s : X86Memory.State) (f : Option Flags) :
    (called s f).core.regs 0=load32 s.memory (s.regs 4+(20#32)) ∧
    (called s f).core.regs 2=s.regs 5 ∧ (called s f).core.regs 3=(0x2ba10#32) ∧
    (called s f).core.regs 4=s.regs 4-(4#32) ∧
    load32 (called s f).core.memory (s.regs 4-(4#32))=(0x2c7a1#32) ∧
    load32 (called s f).core.memory (s.regs 4+(16#32))=s.regs 0 := by
  have adj : Apart (s.regs 4+(20#32)) (s.regs 4+(16#32)) := apart _ _ _ (by unfold Apart; decide)
  have saved : Apart (s.regs 4+(16#32)) (s.regs 4-(4#32)) := by
    simpa only [BitVec.sub_eq_add_neg] using apart (s.regs 4) (16#32) (-(4#32)) (by unfold Apart; decide)
  simp [called,c4,c3,c2,c1,X86Routine.pushWord,put,write,load_store_apart _ _ _ _ adj,
    load_store_apart _ _ _ _ saved,load_store]

def second (s : X86Memory.State) := OriginalDivlineSide.result (called s none).core
def result (s : X86Memory.State) := tested (second s).core

theorem second_returned (s : X86Memory.State) :
    (second s).pc=0x2c7a1 ∧ (second s).core.regs 4=s.regs 4 ∧ (second s).core.regs 1=s.regs 1 ∧
    load32 (second s).core.memory (s.regs 4+(16#32))=s.regs 0 := by
  have c := call_observe s none
  have r := OriginalDivlineSide.returned (called s none).core
  refine ⟨?_,?_,r.2.1,?_⟩
  · have ret : load32 (called s none).core.memory ((called s none).core.regs 4)=(0x2c7a1#32) := by
      rw [c.2.2.2.1]
      exact c.2.2.2.2.1
    exact r.2.2.2.2.2.trans (congrArg BitVec.toNat ret)
  · apply r.1.trans
    rw [c.2.2.2.1]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · apply (OriginalDivlineSide.frame _ _ ?_).trans c.2.2.2.2.2
    rw [c.2.2.2.1]
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (s.regs 4) (16#32) (-(8#32)) (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (s.regs 4) (16#32) (-(12#32)) (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (s.regs 4) (16#32) (-(16#32)) (by unfold Apart; decide)
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using apart (s.regs 4) (16#32) (-(20#32)) (by unfold Apart; decide)

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤53, X86Routine.Prefix program [] n ⟨s,f,0x2c78d⟩ (result s) := by
  have a := call_execution s f
  obtain ⟨n,hn,b⟩ := OriginalDivlineSide.execution (called s f).core f
  have contains (pc : Nat) (h : OriginalDivlineSide.program pc≠none) :=
    (contains_prior pc (by rw [OriginalThingFirstSide.contains_side pc h]; exact h)).trans (OriginalThingFirstSide.contains_side pc h)
  obtain ⟨m,hm,c⟩ := test_execution (second s).core (second s).flags
  rw [OriginalPathXStep.at_pc _ _ (second_returned s).1] at c
  exact ⟨5+n+m,by omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join a (b.transfer program [] contains (by simp))) c⟩

def Safe (sp a : Word) : Prop :=
  Apart a (sp+(16#32)) ∧ ∀ off∈[(4#32),8,12,16,20], Apart a (sp-off)

theorem call_frame (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    load32 (called s none).core.memory a=load32 s.memory a := by
  change load32 (store32 (store32 s.memory (s.regs 4+(16#32)) _) (s.regs 4-(4#32)) _) a=_
  rw [load_store_apart _ _ _ _ (safe.2 (4#32) (by simp)),load_store_apart _ _ _ _ safe.1]

theorem helper_safe (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    ∀ off∈[(4#32),8,12,16], Apart a ((called s none).core.regs 4-off) := by
  rw [(call_observe s none).2.2.2.1]
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (8#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (12#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (16#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.2 (20#32) (by simp)

theorem tested_observe (s : X86Memory.State) :
    (tested s).core.memory=s.memory ∧ (tested s).core.regs 4=s.regs 4 ∧
    (tested s).core.regs 1=s.regs 1 ∧
    (tested s).pc=(if s.regs 0=oldSide s then 0x2c805 else 0x2c7ae) ∧
    (s.regs 0=oldSide s → (tested s).core.regs 0=(1#32)) := by
  by_cases same : s.regs 0=oldSide s <;> simp [tested,same,put,write]

theorem frame (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [show (result s).core.memory=(second s).core.memory from (tested_observe _).1]
  exact (OriginalDivlineSide.frame _ _ (helper_safe s a safe)).trans (call_frame s a safe)

def firstSide (trace : Collision.Divline) (thing : Collision.SolidThing) := trace.pointSide (points trace thing).1 (points trace thing).2.1
def lastSide (trace : Collision.Divline) (thing : Collision.SolidThing) := trace.pointSide (points trace thing).2.2.1 (points trace thing).2.2.2

theorem side_safe (s : X86Memory.State) (a : Word) (before : OriginalThingFirstSide.Safe s a)
    (scratch : Apart a (s.regs 4+(16#32))) : Safe ((OriginalThingFirstSide.result s).core.regs 4) a := by
  change Safe ((OriginalThingFirstSide.result s).core.regs 4) a
  rw [(OriginalThingFirstSide.returned s).2.1]
  exact ⟨scratch,before.2⟩

theorem second_inputs (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (object : Word) (h : OriginalThingFirstSide.Inputs s trace thing object)
    (scratch : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c], Apart a (s.regs 4+(16#32))) :
    OriginalDivlineSide.Inputs (called (OriginalThingFirstSide.result s).core none).core trace
      (points trace thing).2.2.1 (points trace thing).2.2.2 0x2ba10 := by
  let t := (OriginalThingFirstSide.result s).core
  have c := call_observe t none
  have x2 := OriginalThingFirstSide.second_endpoint s
  have diagonal := OriginalThingDiagonal.live_diagonal s trace thing object h.diagonal
  have first := OriginalThingFirstSide.live s trace thing object h
  have keep (a : Word) (ha : a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c]) :=
    (call_frame t a (side_safe s a (h.safe a ha) (scratch a ha))).trans (OriginalThingFirstSide.frame s a (h.safe a ha))
  constructor
  · apply c.1.trans
    rw [(OriginalThingFirstSide.returned s).2.1]
    apply x2.1.trans
    have dx := diagonal.2.2.2
    rw [(OriginalThingDiagonal.diagonal_observe s).2.2.2.2.2,load_store] at dx
    exact dx
  · exact c.2.1.trans first.2.2.2.2
  · exact c.2.2.1
  · exact (keep _ (by simp)).trans h.traceX
  · exact (keep _ (by simp)).trans h.traceY
  · exact (keep _ (by simp)).trans h.diagonal.traceDX
  · exact (keep _ (by simp)).trans h.diagonal.traceDY
  · intro a ha
    exact helper_safe t a (side_safe s a (h.safe a (by simpa using ha)) (scratch a (by simpa using ha)))

def crossing (s : X86Memory.State) := result (OriginalThingFirstSide.result s).core

theorem bit_eq (a b : Bool) : OriginalDivlineSide.bit a=OriginalDivlineSide.bit b ↔ a=b := by
  cases a <;> cases b <;> decide

theorem live (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (object : Word) (h : OriginalThingFirstSide.Inputs s trace thing object)
    (scratch : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c], Apart a (s.regs 4+(16#32))) :
    (crossing s).pc=(if firstSide trace thing=lastSide trace thing then 0x2c805 else 0x2c7ae) ∧
    (firstSide trace thing=lastSide trace thing → (crossing s).core.regs 0=(1#32) ∧
      Collision.thingIntercept trace thing=.ok none) := by
  let t := (OriginalThingFirstSide.result s).core
  have a := OriginalThingFirstSide.live s trace thing object h
  have b := OriginalDivlineSide.live (called t none).core trace _ _ 0x2ba10 (second_inputs s trace thing object h scratch)
  change (second t).core.regs 0=OriginalDivlineSide.bit (lastSide trace thing) at b
  have ret := second_returned t
  have old : oldSide (second t).core=OriginalDivlineSide.bit (firstSide trace thing) := by
    unfold oldSide
    rw [ret.2.1,ret.2.2.2]
    exact a.1
  have same : (second t).core.regs 0=oldSide (second t).core ↔ firstSide trace thing=lastSide trace thing := by
    rw [old,b,bit_eq]
    exact eq_comm
  have observed := tested_observe (second t).core
  refine ⟨?_,?_⟩
  · exact observed.2.2.2.1.trans (by simp only [same])
  · intro eq
    refine ⟨observed.2.2.2.2 (same.mpr eq),?_⟩
    rw [OriginalThingDiagonal.production]
    change (if firstSide trace thing == lastSide trace thing then _ else _)=_
    simp [eq]
    rfl
end Doom.Proofs.OriginalThingSecondSide

import Doom.Proofs.E1M1NoiseRecursive
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1NoiseFrame
open Verification X86 X86Memory X86Control BlockSummary

/-- The five saved registers and the incoming return word. The local scratch
word at entry ESP-24 is deliberately outside this protected set. -/
def slots (s : X86Memory.State) : List Word :=
  [s.regs 4,s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32)]

def savedMemory (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 s.memory
    (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 1))
    (s.regs 4-(12#32)) (s.regs 6)) (s.regs 4-(16#32)) (s.regs 7))
    (s.regs 4-(20#32)) (s.regs 5)

theorem prepared_memory (s : X86Memory.State) :
    (NoiseAlert.prepared s).memory=savedMemory s := by
  simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,
    NoiseAlert.saveTwo,X86Routine.pushWord,put,write,savedMemory,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- Unconditional provenance of every saved word; no alignment or no-wrap
assumption, and no saved register contents are premises. -/
theorem saved_words (s : X86Memory.State) :
    load32 (savedMemory s) (s.regs 4)=load32 s.memory (s.regs 4) ∧
    load32 (savedMemory s) (s.regs 4-(4#32))=s.regs 3 ∧
    load32 (savedMemory s) (s.regs 4-(8#32))=s.regs 1 ∧
    load32 (savedMemory s) (s.regs 4-(12#32))=s.regs 6 ∧
    load32 (savedMemory s) (s.regs 4-(16#32))=s.regs 7 ∧
    load32 (savedMemory s) (s.regs 4-(20#32))=s.regs 5 := by
  have k01 : Apart (s.regs 4) (s.regs 4-(4#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(4#32)) := DeathStack.slots_apart (s.regs 4) 0 1 (by decide)
    simpa only [BitVec.sub_zero] using h
  have k02 : Apart (s.regs 4) (s.regs 4-(8#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(8#32)) := DeathStack.slots_apart (s.regs 4) 0 2 (by decide)
    simpa only [BitVec.sub_zero] using h
  have k03 : Apart (s.regs 4) (s.regs 4-(12#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(12#32)) := DeathStack.slots_apart (s.regs 4) 0 3 (by decide)
    simpa only [BitVec.sub_zero] using h
  have k04 : Apart (s.regs 4) (s.regs 4-(16#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 0 4 (by decide)
    simpa only [BitVec.sub_zero] using h
  have k05 : Apart (s.regs 4) (s.regs 4-(20#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(20#32)) := DeathStack.slots_apart (s.regs 4) 0 5 (by decide)
    simpa only [BitVec.sub_zero] using h
  have k12 : Apart (s.regs 4-(4#32)) (s.regs 4-(8#32)) := DeathStack.slots_apart (s.regs 4) 1 2 (by decide)
  have k13 : Apart (s.regs 4-(4#32)) (s.regs 4-(12#32)) := DeathStack.slots_apart (s.regs 4) 1 3 (by decide)
  have k14 : Apart (s.regs 4-(4#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 1 4 (by decide)
  have k15 : Apart (s.regs 4-(4#32)) (s.regs 4-(20#32)) := DeathStack.slots_apart (s.regs 4) 1 5 (by decide)
  have k23 : Apart (s.regs 4-(8#32)) (s.regs 4-(12#32)) := DeathStack.slots_apart (s.regs 4) 2 3 (by decide)
  have k24 : Apart (s.regs 4-(8#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 2 4 (by decide)
  have k25 : Apart (s.regs 4-(8#32)) (s.regs 4-(20#32)) := DeathStack.slots_apart (s.regs 4) 2 5 (by decide)
  have k34 : Apart (s.regs 4-(12#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 3 4 (by decide)
  have k35 : Apart (s.regs 4-(12#32)) (s.regs 4-(20#32)) := DeathStack.slots_apart (s.regs 4) 3 5 (by decide)
  have k45 : Apart (s.regs 4-(16#32)) (s.regs 4-(20#32)) := DeathStack.slots_apart (s.regs 4) 4 5 (by decide)
  simp only [savedMemory,load_store,load_store_apart _ _ _ _ k01,load_store_apart _ _ _ _ k02,load_store_apart _ _ _ _ k03,load_store_apart _ _ _ _ k04,load_store_apart _ _ _ _ k05,load_store_apart _ _ _ _ k12,load_store_apart _ _ _ _ k13,load_store_apart _ _ _ _ k14,load_store_apart _ _ _ _ k15,load_store_apart _ _ _ _ k23,load_store_apart _ _ _ _ k24,load_store_apart _ _ _ _ k25,load_store_apart _ _ _ _ k34,load_store_apart _ _ _ _ k35,load_store_apart _ _ _ _ k45,and_self ]

/-- A frame at the epilogue boundary, relative to its actual sector entry. -/
structure Saved (entry boundary : X86Memory.State) : Prop where
  sp : boundary.regs 4=entry.regs 4-(24#32)
  words : ∀ a, a ∈ slots entry → load32 boundary.memory a=load32 (savedMemory entry) a

theorem prepared_saved (s : X86Memory.State) : Saved s (NoiseAlert.prepared s) := by
  constructor
  · simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,
      NoiseAlert.saveTwo,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · intro a _; rw [prepared_memory]

theorem Saved.then_frame {entry s t : X86Memory.State} (h : Saved entry s)
    (sp : t.regs 4=s.regs 4) (writes : List Word)
    (frame : PlayerHeight.Frame s.memory t.memory writes)
    (safe : ∀ a, a ∈ slots entry → ∀ b, b ∈ writes → Apart a b) : Saved entry t :=
  ⟨sp.trans h.sp,fun a ha => (frame a (safe a ha)).trans (h.words a ha)⟩

/-- Exact epilogue result from a preserved frame. EAX and EDX remain caller
clobbered; flags are unknown after the stack-cleanup ADD. -/
theorem restores (entry s : X86Memory.State) (h : Saved entry s) :
    (NoiseTraversal.returned s).pc=(load32 entry.memory (entry.regs 4)).toNat ∧
    (NoiseTraversal.returned s).core.regs 4=entry.regs 4+4 ∧
    (NoiseTraversal.returned s).core.regs 3=entry.regs 3 ∧
    (NoiseTraversal.returned s).core.regs 1=entry.regs 1 ∧
    (NoiseTraversal.returned s).core.regs 6=entry.regs 6 ∧
    (NoiseTraversal.returned s).core.regs 7=entry.regs 7 ∧
    (NoiseTraversal.returned s).core.regs 5=entry.regs 5 ∧
    (NoiseTraversal.returned s).core.regs 0=s.regs 0 ∧
    (NoiseTraversal.returned s).core.regs 2=s.regs 2 ∧
    (NoiseTraversal.returned s).core.memory=s.memory ∧
    (NoiseTraversal.returned s).flags=none := by
  obtain ⟨ret,b,c,si,di,bp⟩ := saved_words entry
  have ret := (h.words _ (by simp [slots])).trans ret
  have b := (h.words _ (by simp [slots])).trans b
  have c := (h.words _ (by simp [slots])).trans c
  have si := (h.words _ (by simp [slots])).trans si
  have di := (h.words _ (by simp [slots])).trans di
  have bp := (h.words _ (by simp [slots])).trans bp
  simp [BitVec.sub_eq_add_neg] at ret b c si di bp
  simp [NoiseTraversal.returned,NoiseTraversal.restored,PspriteLoop.popped,
    put,write,h.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc,ret,b,c,si,di,bp]

/-- Sector-object writes must avoid this invocation's saved words. This is an
address condition, not an assumption about the resulting register values. -/
def SectorSafe (entry : X86Memory.State) : Prop :=
  ∀ a, a ∈ slots entry → ∀ b,
    b ∈ [entry.regs 0+(66#32),entry.regs 0+(18#32),entry.regs 0+(22#32)] → Apart a b

private theorem gate_saved {entry s : X86Memory.State} (h : Saved entry s) :
    Saved entry (NoiseAlert.gate s).core := by
  unfold NoiseAlert.gate
  split
  · exact h
  · exact ⟨by simpa [put,write] using h.sp,h.words⟩

/-- Both pruning and fresh/improved-sector updates preserve the frame under
separation. The sector stamp, cost and target are still actually written. -/
theorem sector_saved (entry : X86Memory.State) (safe : SectorSafe entry) :
    Saved entry (E1M1NoiseAlert.sectorResult entry).core := by
  have h := gate_saved (prepared_saved entry)
  have sector : (NoiseAlert.gate (NoiseAlert.prepared entry)).core.regs 3=entry.regs 0 := by
    unfold NoiseAlert.gate
    split <;> simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,
      NoiseAlert.saveTwo,X86Routine.pushWord,put,write]
  simp only [E1M1NoiseAlert.sectorResult]
  split
  · refine h.then_frame (by simp [NoiseAlert.updated,write]) _ (NoiseAlert.update_frame _) ?_
    simpa only [sector,SectorSafe] using safe
  · exact h

/-- Returning from a recursive CALL recovers the parent's real continuation,
stack, sector, block count and line counters. Child frame preservation is still
explicit until the graph-wide separation invariant is established. -/
theorem child_restores (parent boundary : X86Memory.State) (f : Option Flags)
    (h : Saved (NoiseTraversal.recursiveCall parent f).core boundary) :
    (NoiseTraversal.returned boundary).pc=0x27006 ∧
    (NoiseTraversal.returned boundary).core.regs 4=parent.regs 4 ∧
    (NoiseTraversal.returned boundary).core.regs 3=parent.regs 3 ∧
    (NoiseTraversal.returned boundary).core.regs 1=parent.regs 1 ∧
    (NoiseTraversal.returned boundary).core.regs 6=parent.regs 6 ∧
    (NoiseTraversal.returned boundary).core.regs 7=parent.regs 7 ∧
    (NoiseTraversal.returned boundary).core.regs 5=parent.regs 5 := by
  obtain ⟨ret,sp,b,c,si,di,bp,_⟩ := restores _ _ h
  simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,write,load_store,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] at ret sp b c si di bp
  exact ⟨ret,sp,b,c,si,di,bp⟩

/-- The parent's index and pointer offset advance once after a nested return,
regardless of what values the child used in its own loop. -/
theorem child_progress (parent boundary : X86Memory.State) (f : Option Flags)
    (h : Saved (NoiseTraversal.recursiveCall parent f).core boundary) :
    (NoiseTraversal.advanced (NoiseTraversal.returned boundary).core).core.regs 6=parent.regs 6+(1#32) ∧
    (NoiseTraversal.advanced (NoiseTraversal.returned boundary).core).core.regs 5=parent.regs 5+(4#32) := by
  obtain ⟨_,_,_,_,si,_,bp⟩ := child_restores parent boundary f h
  simp [NoiseTraversal.advanced,put,write,si,bp]

/-- Concrete remaining-line measure for an admitted nonwrapping index. This is
local loop progress, not termination of the recursive sector graph. -/
theorem remaining_decreases (s : X86Memory.State) (n : Nat)
    (index : (s.regs 6).toNat<n) (small : n≤2147483647) :
    n-((NoiseTraversal.advanced s).core.regs 6).toNat < n-(s.regs 6).toNat := by
  have step : ((NoiseTraversal.advanced s).core.regs 6).toNat=(s.regs 6).toNat+1 := by
    change ((s.regs 6+(1#32)).toNat)=(s.regs 6).toNat+1
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  rw [step]
  omega

/-- Execute a leaf/pruned child and the parent's next-line step. The return
address and restored counters are derived from CALL/prologue provenance; the
only child-specific premises are the sector endpoint and address separation. -/
theorem terminal_child_execution (parent : X86Memory.State) (f : Option Flags)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core)
    (terminal : (E1M1NoiseAlert.sectorResult (NoiseTraversal.recursiveCall parent f).core).pc=0x27011) :
    E1M1NoiseRecursive.Runs 36 (NoiseTraversal.recursiveCall parent f)
      (NoiseTraversal.advanced (E1M1NoiseTraversal.sectorReturn (NoiseTraversal.recursiveCall parent f).core).core) := by
  let child := NoiseTraversal.recursiveCall parent f
  let r := E1M1NoiseTraversal.sectorReturn child.core
  have saved := sector_saved child.core safe
  have ret : r.pc=0x27006 := (child_restores parent _ f saved).1
  obtain ⟨n,hn,p⟩ := E1M1NoiseTraversal.terminal_sector_execution child.core child.flags terminal
  have p : E1M1NoiseRecursive.Runs 31 child r :=
    ⟨n,hn,p.transfer E1M1NoiseOpening.program [] E1M1NoiseOpening.contains_prior (by simp)⟩
  obtain ⟨m,hm,q⟩ := X86Routine.run_path (NoiseTraversal.advance_execution r.core r.flags)
  have contains (pc : Nat) (h : NoiseTraversal.program pc≠none) :
      E1M1NoiseOpening.program pc=NoiseTraversal.program pc := by
    have prior := E1M1NoiseTraversal.contains_traversal pc h
    rw [E1M1NoiseOpening.contains_prior pc (by rw [prior]; exact h),prior]
  have q := (X86CodeMemory.lift_success q.1 FloorCaller.cm).transfer E1M1NoiseOpening.program [] contains (by simp)
  have eq : r=⟨r.core,r.flags,0x27006⟩ := by rw [←ret]
  rw [←eq] at q
  obtain ⟨n,hn,p⟩ := p
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans p q⟩
end Doom.Proofs.E1M1NoiseFrame

import Doom.Proofs.E1M1NoiseAccounting
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseLineProgress
open Verification X86 X86Memory X86Control BlockSummary E1M1NoisePreservation E1M1NoiseFootprint

def openingGlobals : List Word := [0x2c034,0x2c030,0x2c02c,0x2c038]
/-- Protect precisely the saved sector and index from the opening's global writes.
The offset register EBP is never changed by the helper. -/
def OpeningSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [s.regs 4-(4#32),s.regs 4-(16#32)] openingGlobals

theorem opening_regs (s : X86Memory.State) (safe : OpeningSafe s) :
    (E1M1NoiseOpening.result s).core.regs 3=s.regs 3 ∧
    (E1M1NoiseOpening.result s).core.regs 6=s.regs 6 ∧
    (E1M1NoiseOpening.result s).core.regs 5=s.regs 5 := by
  have keep (a : Word) (ha : a ∈ [s.regs 4-(4#32),s.regs 4-(16#32)])
      (m : Memory) (v : Word) (g : Word) (hg : g ∈ openingGlobals) :=
    load_store_apart m g a v (safe a ha g hg)
  have k12 : Apart (s.regs 4-(4#32)) (s.regs 4-(8#32)) := DeathStack.slots_apart (s.regs 4) 1 2 (by decide)
  have k13 : Apart (s.regs 4-(4#32)) (s.regs 4-(12#32)) := DeathStack.slots_apart (s.regs 4) 1 3 (by decide)
  have k14 : Apart (s.regs 4-(4#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 1 4 (by decide)
  simp only [E1M1NoiseOpening.result]
  split <;> simp [NoiseOpening.closed,NoiseOpening.entry,NoiseOpening.prepared,NoiseOpening.saved,
    NoiseOpening.returned,NoiseOpening.range,NoiseOpening.floor,NoiseOpening.floorInputs,
    NoiseOpening.ceiling,NoiseOpening.ceilingInputs,PspriteLoop.popped,X86Routine.pushWord,put,write,
    ite_true,ite_false,BitVec.sub_sub,BitVec.sub_add_cancel]
  all_goals
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at k12 k13 k14 ⊢
    have keep4 (m : Memory) (v : Word) (g : Word) (hg : g ∈ openingGlobals) :=
      keep (s.regs 4-(4#32)) (by simp) m v g hg
    have keep16 (m : Memory) (v : Word) (g : Word) (hg : g ∈ openingGlobals) :=
      keep (s.regs 4-(16#32)) (by simp) m v g hg
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at keep4 keep16
    simp [keep4,keep16,openingGlobals,load_store_apart _ _ _ _ k12,
      load_store_apart _ _ _ _ k13,load_store_apart _ _ _ _ k14,load_store]


/-- Guard as seen at the caller, before its CALL pushes a return word. -/
def DispatchSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [s.regs 4-(8#32),s.regs 4-(20#32)] openingGlobals

theorem opened_regs (s : X86Memory.State) (f : Option Flags) (safe : DispatchSafe s) :
    (E1M1NoiseOpening.opened s f).core.regs 3=s.regs 3 ∧
    (E1M1NoiseOpening.opened s f).core.regs 6=s.regs 6 ∧
    (E1M1NoiseOpening.opened s f).core.regs 5=s.regs 5 := by
  have h := opening_regs (NoiseTraversal.openingCall s f).core (by
    simpa [OpeningSafe,DispatchSafe,NoiseTraversal.openingCall,X86Routine.pushWord,put,write,BitVec.sub_sub] using safe)
  simpa [E1M1NoiseOpening.opened,NoiseTraversal.openingCall,X86Routine.pushWord,put,write] using h

private theorem neighbor_regs (s : X86Memory.State) :
    (E1M1NoiseOpening.neighbor s).core.regs 3=s.regs 3 ∧
    (E1M1NoiseOpening.neighbor s).core.regs 6=s.regs 6 ∧
    (E1M1NoiseOpening.neighbor s).core.regs 5=s.regs 5 := by
  simp only [E1M1NoiseOpening.neighbor]; split <;>
    simp [NoiseOpening.backNeighbor,NoiseOpening.frontNeighbor,NoiseOpening.neighborGate,NoiseOpening.neighborInputs,put,write]

private theorem line_regs (s : X86Memory.State) (f : Option Flags) (safe : DispatchSafe s) :
    (E1M1NoiseOpening.lineResult s f).core.regs 3=s.regs 3 ∧
    (E1M1NoiseOpening.lineResult s f).core.regs 6=s.regs 6 ∧
    (E1M1NoiseOpening.lineResult s f).core.regs 5=s.regs 5 := by
  have h := opened_regs s f safe
  simp only [E1M1NoiseOpening.lineResult]; split
  · simpa only [(neighbor_regs _).1,(neighbor_regs _).2.1,(neighbor_regs _).2.2,NoiseTraversal.openingGate] using h
  · exact h

private theorem block_regs (s : X86Memory.State) :
    (NoiseTraversal.blockResult s).core.regs 3=s.regs 3 ∧
    (NoiseTraversal.blockResult s).core.regs 6=s.regs 6 ∧
    (NoiseTraversal.blockResult s).core.regs 5=s.regs 5 := by
  simp only [NoiseTraversal.blockResult]; split
  · simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
  · split <;> simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]

/-- Actual line selection/opening/neighbor/block dispatch preserves the parent
sector, index and offset, whether it skips or enters a recursive child. -/
theorem dispatch_regs (s : X86Memory.State) (safe : DispatchSafe s) :
    (E1M1NoiseIteration.dispatched s).core.regs 3=s.regs 3 ∧
    (E1M1NoiseIteration.dispatched s).core.regs 6=s.regs 6 ∧
    (E1M1NoiseIteration.dispatched s).core.regs 5=s.regs 5 := by
  have gate (r : Reg) (hr : r=3 ∨ r=6 ∨ r=5 ∨ r=4) : (NoiseTraversal.lineGate s).core.regs r=s.regs r := by
    rcases hr with rfl|rfl|rfl|rfl <;> simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  have h := line_regs (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags (by
    simpa only [DispatchSafe,gate 4 (by simp)] using safe)
  simp only [gate 3 (by simp),gate 6 (by simp),gate 5 (by simp)] at h
  simp only [E1M1NoiseIteration.dispatched]; split
  · simp only [E1M1NoiseOpening.blockResult]; split
    · simpa only [(block_regs _).1,(block_regs _).2.1,(block_regs _).2.2] using h
    · exact h
  · exact ⟨gate 3 (by simp),gate 6 (by simp),gate 5 (by simp)⟩

def count (s : X86Memory.State) : Nat := (load32 s.memory (s.regs 3+(78#32))).toNat
def remaining (s : X86Control.State) : Nat := count s.core-(s.core.regs 6).toNat

/-- A nonempty admitted sector starts at index zero with its original line
count, provided its prefix writes cannot overwrite that count. -/
theorem start_remaining (s : X86Control.State) (more : (sector s).pc=0x26fa6)
    (safe : ∀ b, b ∈ sectorWrites s.core → Apart (s.core.regs 0+(78#32)) b) :
    remaining (startLines s)=(load32 s.core.memory (s.core.regs 0+(78#32))).toNat := by
  have ch := E1M1NoiseLedger.sector_more_charge s.core more
  have enter : E1M1NoiseLedger.admitted s.core := by
    by_cases h : E1M1NoiseLedger.admitted s.core
    · exact h
    · simp [E1M1NoiseLedger.charge,h] at ch
  have regs : (sector s).core.regs 3=s.core.regs 0 ∧ (sector s).core.regs 6=0 := by
    change (NoiseAlert.gate (NoiseAlert.prepared s.core)).pc=0x26f83 at enter
    simp only [sector,E1M1NoiseAlert.sectorResult,if_pos enter]
    simp only [NoiseAlert.gate]; split <;>
      simp [NoiseAlert.updated,NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,
        NoiseAlert.saveTwo,X86Routine.pushWord,put,write]
  have mem := sector_frame s.core _ safe
  simp [remaining,count,startLines,NoiseTraversal.initialized,put,write,regs.1,regs.2,mem]

/-- Any protected map word, including line count and line-list pointer, is
stable through a complete recursive traversal. -/
theorem map_word {phase s t w} (h : Trace phase s t w) (a : Word)
    (safe : ∀ b, b ∈ w → Apart a b) : load32 t.core.memory a=load32 s.core.memory a := h.frame a safe

/-- Exact one-step decrease, not merely a signed comparison. The upper bound
excludes index wrap and the negative half of the signed loop count domain. -/
theorem advance_remaining (s : X86Control.State)
    (index : (s.core.regs 6).toNat<count s.core) (small : count s.core≤2147483647) :
    remaining (advance s)+1=remaining s := by
  have idx : ((advance s).core.regs 6).toNat=(s.core.regs 6).toNat+1 := by
    change (s.core.regs 6+(1#32)).toNat=_
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  have stable : count (advance s).core=count s.core := by simp [count,advance,NoiseTraversal.advanced,put,write]
  simp only [remaining,stable,idx]
  omega

/-- A skipped line advances the same sector's original line count and index. -/
theorem skip_remaining (s : X86Control.State) (regs : DispatchSafe s.core)
    (safe : ∀ b, b ∈ lineWrites s.core → Apart (s.core.regs 3+(78#32)) b)
    (index : (s.core.regs 6).toNat<count s.core) (small : count s.core≤2147483647) :
    remaining (advance (dispatch s))+1=remaining s := by
  have r := dispatch_regs s.core regs
  have c : count (dispatch s).core=count s.core := by
    simp only [count,dispatch,r.1,dispatch_frame s.core _ safe]
  have h := advance_remaining (dispatch s) (by simpa only [dispatch,r.2.1,c] using index) (by simpa only [c] using small)
  simpa only [remaining,c,dispatch,r.2.1] using h

/-- After a completed child, protection of its saved frame and of the parent's
line-count word derives the parent's exact remaining-line decrease. -/
theorem child_remaining {s u w n layout}
    (child : E1M1NoiseAccounting.CheckedTrace layout .sector (dispatch s) u w n)
    (regs : DispatchSafe s.core)
    (frame : E1M1NoisePreservation.SectorSafe (dispatch s).core w)
    (safe : ∀ b, b ∈ lineWrites s.core++w → Apart (s.core.regs 3+(78#32)) b)
    (index : (s.core.regs 6).toNat<count s.core) (small : count s.core≤2147483647) :
    remaining (advance u)+1=remaining s := by
  have r := dispatch_regs s.core regs
  have restored := child.restores_sector frame
  have b : u.core.regs 3=s.core.regs 3 := restored.b.trans r.1
  have i : u.core.regs 6=s.core.regs 6 := restored.si.trans r.2.1
  have c : count u.core=count s.core := by
    unfold count
    rw [b,child.frame _ (fun a ha => safe a (List.mem_append_right _ ha)),
      dispatch_frame s.core _ (fun a ha => safe a (List.mem_append_left _ ha))]
  have h := advance_remaining u (by simpa only [i,c] using index) (by simpa only [c] using small)
  simpa only [remaining,c,i] using h
end Doom.Proofs.E1M1NoiseLineProgress

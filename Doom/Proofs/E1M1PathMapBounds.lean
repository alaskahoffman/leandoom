import Doom.Proofs.E1M1PathMapLookup
import Doom.Proofs.E1M1LineCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMapBounds
open Verification X86 X86Memory X86Control BlockSummary E1M1PathMap E1M1PathMapLookup

def bytesProgram (entry ret cell : List UInt8) : X86Routine.Program := fun pc =>
  match OriginalLineBounds.bytesProgram entry ret pc with
  | some op => some op
  | none => OriginalLineCell.bytesProgram cell pc

def program := bytesProgram OriginalLineBounds.lineEntry OriginalLineBounds.lineReturn OriginalLineCell.code

theorem contains_bounds (pc : Nat) (h : OriginalLineBounds.program pc≠none) :
    program pc=OriginalLineBounds.program pc := by
  unfold program bytesProgram
  change (match OriginalLineBounds.program pc with | some op => some op | none => _) = _
  cases hp : OriginalLineBounds.program pc <;> simp_all

theorem contains_lookup (pc : Nat) (h : OriginalLineCell.program pc≠none) :
    program pc=OriginalLineCell.program pc := by
  have range : 0x2c541≤pc ∧ pc<0x2c587 := by
    by_cases hr : 0x2c541≤pc ∧ pc<0x2c587
    · exact hr
    · simp [OriginalLineCell.program,OriginalLineCell.bytesProgram,hr] at h
  have lower : ¬(0x2c520≤pc ∧ pc<0x2c541) := by omega
  have upper : ¬(0x2c587≤pc ∧ pc<0x2c591) := by omega
  simp [program,bytesProgram,OriginalLineBounds.bytesProgram,lower,upper,OriginalLineCell.program]

/-- Bounds may push two stack words, but neither branch performs other writes. -/
theorem result_memory (s : X86Memory.State) :
    (OriginalLineBounds.result s).core.memory=(OriginalLineBounds.entry s).memory := by
  unfold OriginalLineBounds.result
  split
  · exact (OriginalLineBounds.guard_frame _).1
  · simpa only [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,
      OriginalLineBounds.r1,put,write] using (OriginalLineBounds.guard_frame (OriginalLineBounds.entry s)).1

def Safe (s : X86Memory.State) (a : Word) : Prop :=
  Apart a (s.regs 4-(4#32)) ∧ Apart a (s.regs 4-(8#32))

theorem result_frame (s : X86Memory.State) (a : Word) (safe : Safe s a) :
    load32 (OriginalLineBounds.result s).core.memory a=load32 s.memory a := by
  rw [result_memory]
  exact OriginalLineBounds.entry_frame s a safe.1 safe.2

def ImageSafe (s : X86Memory.State) (base : Word) (words : Array Nat) : Prop :=
  ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i))

theorem image_preserved (s : X86Memory.State) (base : Word) (words : Array Nat)
    (image : WordImage s.memory base words) (safe : ImageSafe s base words) :
    WordImage (OriginalLineBounds.result s).core.memory base words := by
  intro i value h
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp h
  have keep := congrArg (fun v : Word => v.extractLsb' 0 16) (result_frame s _ (safe i bound))
  rw [SectorDispatch.load_half,SectorDispatch.load_half] at keep
  exact keep.trans (image i value h)

structure Globals (s : X86Memory.State) (base lines : Word) : Prop where
  table : load32 s.memory 0x2c100=base+(8#32)
  lists : load32 s.memory 0x2c10c=base
  lines : load32 s.memory 0x2c120=lines
  safe : ∀ a∈[(0x2c100#32),0x2c10c,0x2c120], Safe s a

/-- The actual bounds code supplies the width register, coordinates and globals
needed by lookup; no interior Context is assumed. -/
theorem lookup_context (s : X86Memory.State) (base lines : Word) (x y : Int32) (w h : Nat)
    (bounds : OriginalLineBounds.Inputs s x y w h) (globals : Globals s base lines)
    (inside : Collision.pathCellInside x y w h=true) :
    Context (OriginalLineBounds.result s).core base x y w := by
  have ins := (OriginalLineBounds.live_bounds s x y w h bounds).mpr inside
  have ew := OriginalLineBounds.entry_frame s (0x2c0fc#32) (bounds.safe _ (by simp)).1 (bounds.safe _ (by simp)).2
  rw [E1M1LineCell.inside_state s ins]
  constructor
  · simpa [OriginalLineBounds.loaded,put,write,(OriginalLineBounds.entry_coordinates s).1] using bounds.mapX
  · simpa [OriginalLineBounds.loaded,put,write,(OriginalLineBounds.entry_coordinates s).2.1] using bounds.mapY
  · simpa [OriginalLineBounds.loaded,OriginalLineBounds.width,put,write,ew] using bounds.width
  · exact (OriginalLineBounds.entry_frame s _ (globals.safe _ (by simp)).1 (globals.safe _ (by simp)).2).trans globals.table
  · exact (OriginalLineBounds.entry_frame s _ (globals.safe _ (by simp)).1 (globals.safe _ (by simp)).2).trans globals.lists

def scanStart (s : X86Memory.State) := OriginalLineCell.lookup (OriginalLineBounds.result s).core

/-- Inside-cell execution joins the real prologue and signed bounds tests to
lookup. All map and pointer representation premises refer to iterator entry. -/
theorem inside_to_scan (s : X86Memory.State) (f : Option Flags) (base lines : Word)
    (words : Array Nat) (c : Cell) (x y : Int32) (w h : Nat)
    (bounds : OriginalLineBounds.Inputs s x y w h) (globals : Globals s base lines)
    (inside : Collision.pathCellInside x y w h=true)
    (valid : c.Valid words) (image : WordImage s.memory base words) (safe : ImageSafe s base words)
    (selected : words[4+Collision.pathCellIndex x y w]?=some c.offset) :
    (∃ n≤24, X86Routine.Prefix program [] n ⟨s,f,0x2c520⟩ (scanStart s)) ∧
    ScanWords (scanStart s).core lines c ∧ (scanStart s).pc=0x2c57f ∧
    (scanStart s).core.regs 4=s.regs 4-(8#32) := by
  have context := lookup_context s base lines x y w h bounds globals inside
  have retained := image_preserved s base words image safe
  have lb := (result_frame s _ (globals.safe _ (by simp))).trans globals.lines
  obtain ⟨lookup,items⟩ := lookup_to_scan (OriginalLineBounds.result s).core (OriginalLineBounds.result s).flags
    base lines words c x y w h context inside valid retained selected lb
  have ins := (OriginalLineBounds.live_bounds s x y w h bounds).mpr inside
  have pc : (OriginalLineBounds.result s).pc=0x2c541 := by rw [E1M1LineCell.inside_state s ins]
  rw [OriginalPathXStep.at_pc _ _ pc] at lookup
  obtain ⟨n,hn,entry⟩ := OriginalLineBounds.execution s f
  have joined := OriginalGroupBounds.prefix_join
    (entry.transfer program [] contains_bounds (by simp))
    (lookup.transfer program [] contains_lookup (by simp))
  refine ⟨⟨n+8,by omega,joined⟩,items,(OriginalLineCell.lookup_observe _).2.2.2,?_⟩
  rw [show (scanStart s).core.regs 4=(OriginalLineBounds.result s).core.regs 4 from
    (OriginalLineCell.lookup_observe _).2.2.1,E1M1LineCell.inside_state s ins]
  exact (OriginalLineBounds.entry_coordinates s).2.2

/-- Outside cells return true without any BLOCKMAP image or lookup premises. -/
theorem outside_returns (s : X86Memory.State) (f : Option Flags) (x y : Int32) (w h : Nat)
    (bounds : OriginalLineBounds.Inputs s x y w h) (outside : Collision.pathCellInside x y w h=false) :
    (∃ n≤16, X86Routine.Prefix program [] n ⟨s,f,0x2c520⟩ (OriginalLineBounds.result s)) ∧
    (OriginalLineBounds.result s).core.regs 0=1 ∧
    (OriginalLineBounds.result s).core.regs 4=s.regs 4+4 ∧
    (OriginalLineBounds.result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  obtain ⟨n,hn,path⟩ := OriginalLineBounds.execution s f
  refine ⟨⟨n,hn,path.transfer program [] contains_bounds (by simp)⟩,?_⟩
  apply OriginalLineBounds.outside_return
  intro ins
  have yes := (OriginalLineBounds.live_bounds s x y w h bounds).mp ins
  simp [outside] at yes

/-- Only records already occupied and the append cursor need protection from
these two stack writes; no extra capacity is assumed or consumed. -/
theorem collection_preserved (s : X86Memory.State) (base : Word)
    (resolver : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolver hits reserve)
    (cursorSafe : Safe s (0x2c028#32))
    (recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8], Safe s (base+BitVec.ofNat 32 (12*i)+off)) :
    OriginalLineCollection.Tracks (scanStart s).core base resolver hits reserve := by
  apply lookup_preserves_collection
  refine ⟨?_,?_,tracked.room⟩
  · intro i hi
    obtain ⟨frac,line,ptr⟩ := tracked.encoded i hi
    unfold OriginalLineFinish.RecordAt
    rw [result_frame s _ (by simpa only [BitVec.add_zero] using recordsSafe i hi (0#32) (by simp)),
      result_frame s _ (recordsSafe i hi (4#32) (by simp)),result_frame s _ (recordsSafe i hi (8#32) (by simp))]
    exact ⟨frac,line,ptr⟩
  · change load32 (OriginalLineBounds.result s).core.memory (0x2c028#32)=_
    rw [result_frame s _ cursorSafe]
    exact tracked.cursor
end Doom.Proofs.E1M1PathMapBounds

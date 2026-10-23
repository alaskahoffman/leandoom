import Doom.Proofs.E1M1NoiseFuelBound
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseFuelFixture
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseVisits E1M1NoiseLedger E1M1NoiseAccounting
open E1M1NoisePreservation

def origin : Word := 0x600101
def other : Word := 0x600201
def wall : Word := 0x601001
def sides : Word := 0x600801
-- A real two-sided open line back to the same sector, with unaligned addresses
-- and a stack that wraps through address zero. The second ledger sector is idle.
def initial : X86Control.State :=
  ⟨⟨fun r => if r=0 then origin else if r=2 then 0 else if r=4 then 1 else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,7),(0x2b958,0x600d01),(0x2c118,sides),(1,0x28000),
      (origin,0),(origin+4,128),(origin+66,6),(origin+18,0),(origin+22,0),
      (other+66,6),(other+18,0),
      (origin+78,1),(origin+82,0x600b01),(0x600b01,wall),
      (wall+16,4),(wall+22,65536),(wall+46,origin),(wall+50,origin),
      (sides+14,origin),(sides+32,origin)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26f60⟩
def layout := [origin,other]
def ledger : Ledger := [(origin,.unseen),(other,.unseen)]
def parent := startLines initial
def called := dispatch parent
def childEnd := finish (sector called)
def result := finish (advance childEnd)
def footprint := E1M1NoiseFootprint.sectorWrites initial.core ++
  (E1M1NoiseFootprint.lineWrites parent.core ++ E1M1NoiseFootprint.sectorWrites called.core)

local instance (a b : Word) : Decidable (BlockSummary.Apart a b) := by unfold BlockSummary.Apart; infer_instance
local instance (a : Word) (writes : List Word) : Decidable (∀ b, b ∈ writes → BlockSummary.Apart a b) :=
  List.decidableBAll (BlockSummary.Apart a) writes
local instance (reads writes : List Word) : Decidable (Protect reads writes) :=
  List.decidableBAll (fun a => ∀ b, b ∈ writes → BlockSummary.Apart a b) reads
local instance (xs : List Word) (s : X86Memory.State) :
    Decidable (∀ a, a ∈ xs → Protect (markReads a) (stackWrites s)) :=
  List.decidableBAll (fun a => Protect (markReads a) (stackWrites s)) xs
local instance (xs : List Word) (s : X86Memory.State) :
    Decidable (∀ a, a ∈ xs → a≠s.regs 0 → Protect (markReads a) (markWrites s)) :=
  List.decidableBAll (fun a => a≠s.regs 0 → Protect (markReads a) (markWrites s)) xs
local instance (s : X86Memory.State) : Decidable (LineSafe layout s) := by
  letI : Decidable (∀ a, a ∈ layout → Protect (markReads a) (E1M1NoiseFootprint.lineWrites s)) :=
    List.decidableBAll (fun a => Protect (markReads a) (E1M1NoiseFootprint.lineWrites s)) layout
  unfold LineSafe; infer_instance
local instance (g a : Word) (mem : Memory) (m : Mark) : Decidable (Rep g a mem m) := by cases m <;> unfold Rep <;> infer_instance
local instance (g : Word) (mem : Memory) (xs : Ledger) : Decidable (Represents g mem xs) := by
  letI : Decidable (∀ p, p ∈ xs → Rep g p.1 mem p.2) := List.decidableBAll (fun p => Rep g p.1 mem p.2) xs
  unfold Represents; infer_instance

theorem initial_safe : E1M1NoiseLedger.SectorSafe layout initial.core := by
  constructor <;> decide +kernel
theorem child_safe : E1M1NoiseLedger.SectorSafe layout called.core := by
  constructor <;> decide +kernel
theorem parent_safe : LineSafe layout parent.core := by decide +kernel
theorem initial_rep : Represents (7#32) initial.core.memory ledger := by decide +kernel

theorem checked : CheckedTrace layout .sector initial result footprint 1 := by
  have child : CheckedTrace layout .sector called childEnd (E1M1NoiseFootprint.sectorWrites called.core) 0 := by
    have count : charge called.core=0 := by decide +kernel
    simpa only [count,childEnd] using CheckedTrace.sectorDone called (by decide +kernel) child_safe
  have body := CheckedTrace.childDone parent childEnd _ 0 (by decide +kernel) (by decide +kernel)
    parent_safe child (by decide +kernel) (by decide +kernel)
  have count : charge initial.core=1 := by decide +kernel
  simpa only [count,Nat.zero_add,footprint] using
    CheckedTrace.sectorMore initial result _ 0 (by decide +kernel) initial_safe body

open E1M1NoiseFuelBound E1M1NoiseLineProgress
local instance (s : X86Memory.State) : Decidable (DispatchSafe s) := by unfold DispatchSafe; infer_instance
local instance (s : X86Memory.State) (w : List Word) : Decidable (SafeWords s w) :=
  List.decidableBAll (fun a => ∀ b, b ∈ w → BlockSummary.Apart a b) (E1M1NoiseFrame.slots s)
local instance (s : X86Memory.State) (w : List Word) : Decidable (E1M1NoisePreservation.SectorSafe s w) := by
  unfold E1M1NoisePreservation.SectorSafe; infer_instance

theorem child_trace : CheckedTrace layout .sector called childEnd (E1M1NoiseFootprint.sectorWrites called.core) 0 := by
  have c : charge called.core=0 := by decide +kernel
  simpa only [c,childEnd] using CheckedTrace.sectorDone called (by decide +kernel) child_safe

theorem child_progress : remaining (advance childEnd)+1=remaining parent := by
  apply E1M1NoiseLineProgress.child_remaining child_trace
  all_goals decide +kernel

theorem loop_guards : LoopGuards 1 checked := by
  have cc : charge called.core=0 := by decide +kernel
  have ic : charge initial.core=1 := by decide +kernel
  have cl : LoopGuards 1 child_trace := by
    have g := LoopGuards.sectorDone (limit:=1) called (by decide +kernel) child_safe
    simpa only [cc,childEnd] using g
  have bl := LoopGuards.childDone parent childEnd _ 0 (by decide +kernel) (by decide +kernel)
    parent_safe child_trace (by decide +kernel) (by decide +kernel) (by decide +kernel) cl
  have entry : remaining (startLines initial)≤1 := by
    rw [start_remaining initial (by decide +kernel) (by decide +kernel)]
    decide +kernel
  have g := LoopGuards.sectorMore initial result _ 0 (by decide +kernel) initial_safe _ entry bl
  simpa only [ic,Nat.zero_add,footprint] using g

example : E1M1NoiseRecursive.eval 9 .sector initial=some result :=
  sector_budget (limit:=1) checked loop_guards 7 ledger rfl initial_rep
example : E1M1NoiseRecursive.Runs (E1M1NoiseRecursive.bound 9) initial result :=
  sector_execution (limit:=1) checked loop_guards 7 ledger rfl initial_rep rfl
example : E1M1NoiseRecursive.eval 3 .sector initial=some result := at_allowance (limit:=1) loop_guards

-- A skipped line with two remaining entries exercises the other progress route.
def skipped : X86Control.State :=
  ⟨⟨fun r => if r=3 then origin else if r=4 then 0x1000 else 0,
    ([(origin+78,3),(origin+82,0x600b01),(0x600b01,wall),(0x600b05,wall),(0x600b09,wall)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26fa8⟩
example : remaining (advance (dispatch skipped))+1=remaining skipped := by
  apply skip_remaining skipped
  all_goals decide +kernel
example : remaining (advance (dispatch skipped))=2 ∧ (advance (dispatch skipped)).pc=0x26fa8 := by decide +kernel

-- A complete three-line skip loop uses both recursive tail constructors.
def skipOne := advance (dispatch skipped)
def skipTwo := advance (dispatch skipOne)
def skipEnd := finish (advance (dispatch skipTwo))
def skipWrites := E1M1NoiseFootprint.lineWrites skipped.core ++
  (E1M1NoiseFootprint.lineWrites skipOne.core ++ E1M1NoiseFootprint.lineWrites skipTwo.core)
theorem skip_trace : CheckedTrace layout .lines skipped skipEnd skipWrites 0 := by
  have last := CheckedTrace.lineDone (layout:=layout) skipTwo (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have mid := CheckedTrace.lineMore skipOne skipEnd _ 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) last
  exact CheckedTrace.lineMore skipped skipEnd _ 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) mid
theorem skip_loops : LoopGuards 0 skip_trace := by
  have last := LoopGuards.lineDone (limit:=0) (layout:=layout) skipTwo (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have mid := LoopGuards.lineMore skipOne skipEnd _ 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel) last
  exact LoopGuards.lineMore skipped skipEnd _ 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel) mid
example : E1M1NoiseRecursive.eval 4 .lines skipped=some skipEnd := at_allowance (limit:=0) skip_loops

-- Last valid signed index, still without wrapping; the next step must exit.
def lastLine : X86Control.State :=
  { skipped with core := { skipped.core with regs := write skipped.core.regs 6 (2147483646#32), memory := store32 skipped.core.memory (origin+78) (2147483647#32) } }
example : remaining (advance lastLine)+1=remaining lastLine := advance_remaining lastLine (by decide +kernel) (by decide +kernel)
example : remaining (advance lastLine)=0 ∧ (advance lastLine).pc=0x27011 := by decide +kernel
end Doom.Verification.NoiseFuelFixture

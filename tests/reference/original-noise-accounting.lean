import Doom.Proofs.E1M1NoiseAccounting
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseAccountingFixture
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

-- An independent evaluator check ties the fixture to the executable summaries.
theorem evaluated : E1M1NoiseRecursive.eval 3 .sector initial=some result := by rfl

example : ∃ ys, addresses ys=layout ∧ Represents (7#32) result.core.memory ys ∧ 1+credit ys≤credit ledger :=
  checked.accounting 7 ledger rfl initial_rep
example : (1 : Nat)≤2*layout.length := checked.admission_bound 7 ledger rfl initial_rep
example : Represents (7#32) result.core.memory [(origin,.clear),(other,.unseen)] := by decide +kernel
example : result.pc=0x28000 ∧ result.core.regs 4=5 ∧ result.core.regs 3=13 := by decide +kernel
example : E1M1NoiseRecursive.Runs (E1M1NoiseRecursive.bound 3) initial result :=
  E1M1NoiseRecursive.execution 3 .sector initial result rfl evaluated
-- Duplicate ledger entries conservatively inflate credit, but still refine memory.
example : credit (update origin false [(origin,.unseen),(origin,.unseen),(other,.blocked)])=1 := by decide
end Doom.Verification.NoiseAccountingFixture

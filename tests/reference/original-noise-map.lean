import Doom.Proofs.E1M1NoiseMapGuards
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseMapFixture
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

open E1M1NoiseMap

def mainSector : SectorLines := ⟨origin,0x600b01,[wall]⟩
def idleSector : SectorLines := ⟨other,0,[]⟩
def table : List SectorLines := [mainSector,idleSector]
theorem represented : MapRep table initial.core.memory := by
  intro e he
  simp only [table,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> constructor <;> decide +kernel
theorem bounded : Bounded table 1 := by simp [Bounded,table,mainSector,idleSector]

theorem memory_guards : E1M1NoiseMapGuards.MemoryGuards table checked := by
  have cc : charge called.core=0 := by decide +kernel
  have ic : charge initial.core=1 := by decide +kernel
  have child : CheckedTrace layout .sector called childEnd (E1M1NoiseFootprint.sectorWrites called.core) 0 := by
    simpa only [cc,childEnd] using CheckedTrace.sectorDone called (by decide +kernel) child_safe
  have cg : E1M1NoiseMapGuards.MemoryGuards table child := by
    have g := E1M1NoiseMapGuards.MemoryGuards.sectorDone (table:=table) called (by decide +kernel) child_safe (by decide +kernel)
    simpa only [cc,childEnd] using g
  have bg := E1M1NoiseMapGuards.MemoryGuards.childDone (table:=table) parent childEnd _ 0 (by decide +kernel) (by decide +kernel)
    parent_safe child (by decide +kernel) (by decide +kernel) (by decide +kernel) cg
  have g := E1M1NoiseMapGuards.MemoryGuards.sectorMore (table:=table) initial result _ 0 (by decide +kernel) initial_safe _ (by decide +kernel) bg
  simpa only [ic,Nat.zero_add,footprint] using g

example : E1M1NoiseFuelBound.LoopGuards 1 checked := memory_guards.loops 1 bounded represented trivial
example : MapRep table result.core.memory := memory_guards.preserves_map represented
example : E1M1NoiseRecursive.eval 9 .sector initial=some result :=
  E1M1NoiseMapGuards.sector_budget (table:=table) checked memory_guards 1 bounded represented 7 ledger rfl initial_rep

-- Sector entry derives a live cursor and the actual array element selected.
theorem start_facts : MapRep table parent.core.memory ∧ Cursor mainSector parent.core ∧
    E1M1NoiseLineProgress.remaining parent≤1 := by
  exact start_step (table:=table) (limit:=1) (by simp [table]) represented rfl bounded (by decide +kernel) (by decide +kernel)
example : (NoiseTraversal.selected parent.core).regs 2=wall :=
  start_facts.2.1.selected (start_facts.1 mainSector (by simp [table]))

-- Three distinct line pointers make an off-by-one array selection observable.
def triples : SectorLines := ⟨origin,0x600b01,[wall,wall+64,wall+128]⟩
def tripleState : X86Control.State :=
  ⟨⟨fun r => if r=3 then origin else if r=4 then 0x1000 else 0,
    ([(origin+78,3),(origin+82,0x600b01),(0x600b01,wall),(0x600b05,wall+64),(0x600b09,wall+128)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26fa8⟩
theorem triples_rep : MapRep [triples] tripleState.core.memory := by
  intro e he
  have eq : e=triples := List.mem_singleton.mp he
  subst e
  constructor <;> decide +kernel
theorem triples_cursor : Cursor triples tripleState.core := by constructor <;> decide +kernel
local instance (s : X86Memory.State) : Decidable (E1M1NoiseLineProgress.DispatchSafe s) := by
  unfold E1M1NoiseLineProgress.DispatchSafe; infer_instance

theorem skipped : MapRep [triples] (advance (dispatch tripleState)).core.memory ∧
    Cursor triples (advance (dispatch tripleState)).core ∧
    E1M1NoiseLineProgress.remaining (advance (dispatch tripleState))+1=E1M1NoiseLineProgress.remaining tripleState := by
  exact skip_step (table:=[triples]) (by simp) triples_rep triples_cursor (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (NoiseTraversal.selected (advance (dispatch tripleState)).core).regs 2=wall+64 :=
  skipped.2.1.selected (skipped.1 triples (by simp))
example : (advance tripleState).pc=0x26fa8 ↔ (tripleState.core.regs 6).toNat+1<triples.lines.length :=
  triples_cursor.advance_branch (triples_rep triples (by simp)) (by decide +kernel)
-- A self-call with another parent line still to visit exercises resumption.
def doubleSector : SectorLines := ⟨origin,0x600b01,[wall,wall]⟩
def doubleTable := [doubleSector,idleSector]
def doubleInitial : X86Control.State := { initial with core := { initial.core with
  memory := store32 (store32 initial.core.memory (origin+78) 2) (0x600b05#32) wall } }
def doubleParent := startLines doubleInitial
def doubleCall := dispatch doubleParent
def doubleReturn := finish (sector doubleCall)
theorem double_rep : MapRep doubleTable doubleInitial.core.memory := by
  intro e he
  simp only [doubleTable,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> constructor <;> decide +kernel
theorem double_start : MapRep doubleTable doubleParent.core.memory ∧ Cursor doubleSector doubleParent.core ∧
    E1M1NoiseLineProgress.remaining doubleParent≤2 := by
  exact start_step (table:=doubleTable) (limit:=2) (by simp [doubleTable]) double_rep rfl
    (by simp [Bounded,doubleTable,doubleSector,idleSector]) (by decide +kernel) (by decide +kernel)
theorem double_child : CheckedTrace layout .sector doubleCall doubleReturn (E1M1NoiseFootprint.sectorWrites doubleCall.core) 0 := by
  have safe : E1M1NoiseLedger.SectorSafe layout doubleCall.core := by constructor <;> decide +kernel
  have charge : E1M1NoiseLedger.charge doubleCall.core=0 := by decide +kernel
  simpa only [charge,doubleReturn] using CheckedTrace.sectorDone doubleCall (by decide +kernel) safe
local instance (s : X86Memory.State) (w : List Word) : Decidable (SafeWords s w) :=
  List.decidableBAll (fun a => ∀ b, b ∈ w → BlockSummary.Apart a b) (E1M1NoiseFrame.slots s)
local instance (s : X86Memory.State) (w : List Word) : Decidable (E1M1NoisePreservation.SectorSafe s w) := by
  unfold E1M1NoisePreservation.SectorSafe; infer_instance
theorem resumed : MapRep doubleTable (advance doubleReturn).core.memory ∧
    Cursor doubleSector (advance doubleReturn).core ∧
    E1M1NoiseLineProgress.remaining (advance doubleReturn)+1=E1M1NoiseLineProgress.remaining doubleParent := by
  exact child_step (table:=doubleTable) (by simp [doubleTable]) double_start.1 double_start.2.1
    (by decide +kernel) (by decide +kernel) double_child (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (NoiseTraversal.selected (advance doubleReturn).core).regs 2=wall :=
  resumed.2.1.selected (resumed.1 doubleSector (by simp [doubleTable]))
end Doom.Verification.NoiseMapFixture

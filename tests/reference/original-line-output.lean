import Doom.Proofs.E1M1LineOutput
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.LineOutputFixture
open X86 X86Memory X86Control Doom.Proofs E1M1LineScan BlockSummary

-- Two raw records share vertices; the first is vertical, the second diagonal.
-- Distinct raw/runtime strides and a wrapping, unaligned stack are deliberate.
def words : List (Word × Word) :=
  [(0x2c134,2),(0x2c138,0x8000),(0x2c118,0x9000),
   (0x8000,0),(0x8004,0),(0x8008,0),(0x800c,65536),
   (0x8010,65536),(0x8014,131072),(0x900e,0xa000),(0x9020,0xb000)]
def halves : List (Word × BitVec 16) :=
  [(0x6000,0),(0x6002,1),(0x6004,7),(0x6006,8),(0x6008,9),
   (0x600a,0),(0x600c,65535),
   (0x600e,1),(0x6010,2),(0x6012,10),(0x6014,11),(0x6016,12),
   (0x6018,1),(0x601a,0)]
def memory : Memory := halves.foldl (fun m (a,v) => X86Routine.store16 m a v)
  (words.foldl (fun m (a,v) => store32 m a v) (fun _ => 0x5a))
def initial : X86Memory.State :=
  ⟨fun r => if r=1 then 0x6000 else if r=3 then 0x7000 else if r=4 then 2 else 0,memory⟩

theorem layout : Layout 2 0x7000 2 := by
  refine ⟨by decide,?_⟩
  intro i bound
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl|rfl
  all_goals constructor
  all_goals simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals simp only [Apart,HalfMemory.Separate]
  all_goals decide +kernel +revert

theorem ready : Ready 2 0x6000 0x7000 2 0 initial := by
  constructor <;> decide +kernel +revert

open E1M1LineSource

def records (i : Fin 2) : Record :=
  if i.val=0 then ⟨0,1,0,0,0,65536⟩ else ⟨1,2,0,65536,65536,131072⟩
theorem image : Image records 0x6000 0x8000 initial.memory := by
  intro ⟨i,hi⟩
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl|rfl
  all_goals constructor <;> decide +kernel +revert

theorem separated : ImageLayout records 0x6000 0x8000 0x7000 2 := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  have ii : i=0 ∨ i=1 := by omega
  have jj : j=0 ∨ j=1 := by omega
  rcases ii with rfl|rfl <;> rcases jj with rfl|rfl
  all_goals simp only [Separated,reads,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals constructor
  all_goals simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,Apart,HalfMemory.Separate]
  all_goals decide +kernel +revert

theorem good_records (i : Fin 2) : good (records i)=true := by
  rcases i with ⟨i,hi⟩
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl|rfl <;> decide +kernel +revert

-- Success is derived solely from initial data and static storage facts.
theorem complete : X86Routine.run E1M1LineIteration.program [0x2e3c1] 208
    ⟨initial,none,0x2e29a⟩=some (states initial none 2) :=
  (scan_from_image (total:=2) (records:=records) (raw:=0x6000) (base:=0x8000)
    (line:=0x7000) (sp:=2) (s:=initial) (f:=none)
    layout ready separated image good_records (by decide)).1

-- A wrong decoded vertex cannot silently satisfy the initial relation.
example : ¬Source ⟨0,1,0,0,1,65536⟩ 0x6000 0x8000 initial.memory := by
  intro h
  have falseX : load32 initial.memory (address 0x8000 1)≠1 := by decide +kernel +revert
  exact falseX h.x2

-- The actual signed-index convention is retained (not unsigned indexing).
example : address 0x8000 65535=0x7ff8 := by decide +kernel +revert
#print axioms complete
#print axioms separated


def sides (i : Fin 2) : E1M1LineOutput.Sides :=
  if i.val=0 then ⟨0,65535,0xa000,0⟩ else ⟨1,0,0xb000,0xa000⟩
theorem side_image : E1M1LineOutput.Image sides 0x6000 0x9000 initial.memory := by
  intro ⟨i,hi⟩
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl|rfl
  all_goals constructor <;> decide +kernel +revert

theorem side_separated : E1M1LineOutput.ImageLayout sides 0x6000 0x9000 0x7000 2 := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  have ii : i=0 ∨ i=1 := by omega
  have jj : j=0 ∨ j=1 := by omega
  rcases ii with rfl|rfl <;> rcases jj with rfl|rfl
  all_goals simp [E1M1LineOutput.Separated,E1M1LineOutput.reads,E1M1LineOutput.sideReads,sides]
  all_goals repeat' apply And.intro
  all_goals constructor
  all_goals simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,Apart,HalfMemory.Separate]
  all_goals decide +kernel +revert

theorem storage : E1M1LineOutput.OutputLayout 2 0x7000 2 := by
  intro ⟨i,hi⟩ ⟨j,hj⟩ lt off mem
  have ei : i=0 := by change i<j at lt; omega
  have ej : j=1 := by change i<j at lt; omega
  subst i; subst j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl
  all_goals constructor
  all_goals simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,Apart,HalfMemory.Separate]
  all_goals decide +kernel +revert

theorem grouping :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] 208 ⟨initial,none,0x2e29a⟩=some (states initial none 2) ∧
    (states initial none 2).pc=0x2e3c1 ∧
    OriginalGroupOutput.Inputs (E1M1LineOutput.lines sides 0x7000) (states initial none 2).core.memory :=
  E1M1LineOutput.scan_to_grouping (total:=2) (geometry:=records) (records:=sides)
    (raw:=0x6000) (vertexBase:=0x8000) (sideBase:=0x9000) (output:=0x7000) (sp:=2) (s:=initial) (f:=none)
    layout ready separated image good_records side_separated side_image storage (by decide)

-- Both completed records survive, including absent back and shared front/back.
example : load32 (states initial none 2).core.memory 0x702e=0xa000 ∧
    load32 (states initial none 2).core.memory 0x7032=0 ∧
    load32 (states initial none 2).core.memory 0x706c=0xb000 ∧
    load32 (states initial none 2).core.memory 0x7070=0xa000 := by decide +kernel

-- The absent side makes no phantom memory read.
example : E1M1LineOutput.sideReads 0x9000 65535=[] := by decide +kernel
#print axioms grouping
#print axioms side_separated
#print axioms storage
end Doom.Verification.LineOutputFixture

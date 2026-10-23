import Doom.Proofs.OriginalLineScan
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineSecondPoint
namespace LineScanFixtures
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
inductive Mode where
  | negative | shortStop | wideStop
  deriving DecidableEq

def ray (wide : Mode) (same : Bool) : Collision.Divline :=
  match wide with
  | .negative => ⟨⟨65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
  | .shortStop => ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
  | .wideStop => ⟨⟨-65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
def mem (wide : Mode) (same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x60023e,0x600420),(0x600242,0x600430),(0x600246,0),(0x60024a,65536),
   (0x600420,4194304),(0x600424,131072),(0x600430,4194304),(0x600434,196608),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray wide same).x.raw.toBitVec),(0x2ba14,(ray wide same).y.raw.toBitVec),
   (0x2ba18,(ray wide same).dx.raw.toBitVec),(0x2ba1c,(ray wide same).dy.raw.toBitVec),
   (0x600100,0xdeadbeef),(0x600104,0x2c5f0),(0x600108,777),(0x60010c,0x4f000),(0x13580,99),(0x2c120,0x600200),(0x2c024,4),(0x600900,if wide=.negative then 0xffff0000 else 0x7fff0000),(0x600904,0xffff0001),(0x600110,111),(0x600114,222),(0x600118,333),(0x60011c,444),
   (0x600120,555),(0x600124,0x4f000),(0x2c028,0x70080c),(0x700800,123),(0x700804,1),(0x700808,0x600500)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (wide : Mode) (same : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then OriginalLineSide.bit (firstSide (ray wide same) wall)
    else if r=1 then 0x600200 else if r=4 then 0x600100 else BitVec.ofNat 32 (r.val*11),mem wide same⟩


def iterator (wide : Mode) : X86Memory.State :=
  ⟨fun r => if r=2 then 0x600900 else if r=4 then 0x600104 else 0,mem wide false⟩
def callback (wide : Mode) := OriginalLineDispatch.view (iterator wide)
def fraction (wide : Mode) : Fixed :=
  match wide with
  | .negative => ⟨-2048⟩
  | .shortStop => ⟨43690⟩
  | .wideStop => ⟨2048⟩

theorem inputs (wide : Mode) : OriginalLineCrossing.Inputs (callback wide) (ray wide false) wall 0x600200 0x600400 0x600410 := by
  cases wide
  all_goals
    constructor
    · constructor <;> try decide
      intro a ha off ho
      simp only [OriginalLineInterceptEntry.reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases ho with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    · constructor <;> try decide
      intro a ha off ho
      simp only [OriginalLineSecondPoint.reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    · decide

open OriginalLineCollection
open OriginalLineMixedInvariant
open OriginalLineScan

def oldHit : Collision.Intercept := ⟨⟨123⟩,true,17⟩
def resolve (hit : Collision.Intercept) : Word := if hit.id=17 then 0x600500 else 0x600200
def collected (wide : Mode) : Collision.PathResult := {trace:=ray wide false,collected:=#[oldHit]}
def candidate (wide : Mode) : Candidate :=
  ⟨ray wide false,wall,0x600200,0x600400,0x600410,fraction wide,4,0,true⟩
def protectedWords : List Word :=
  OriginalLineSecondPoint.reads 0x600200 0x600400 0x600410 ++
  OriginalLineSecondPoint.reads 0x60023e 0x600420 0x600430 ++
  [0x600232,0x600270,0x2c024,0x600104,0x13580,0x2c120,0x600900,0x600902,0x600904,0x600906,0x600108,0x60010c]

theorem indexedStack (wide : Mode) (i : Nat) :
    (OriginalLineDispatch.view (atIndex (iterator wide) i)).regs 4=(0x600100#32) :=
  (OriginalLineDispatch.entry_regs _).2.2.trans (by change (0x600104#32)-(4#32)=_; decide)

def writes : List Word := [0x600236,0x600274,0x600100,0x6000fc,0x6000f8,0x6000f4,0x6000f0,0x6000ec,0x6000e8,0x6000e4,0x6000e0,0x6000dc,0x6000d8,0x6000d4,0x6000d0,0x6000cc,0x6000c8,0x6000c4,0x6000c0,0x6000bc,0x6000b8,0x6000b4]

theorem wordWrites (a : Word) (ha : a∈protectedWords) (b : Word) (hb : b∈writes) : Apart a b := by
  simp only [protectedWords,OriginalLineSecondPoint.reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem below_storage (i : Nat) (hi : i<128) (off : Word) (ho : off∈[(0#32),4,8])
    (a : Word) (ha : a.toNat≤0x7007fc) : Apart (slot 0x700800 i off) a := by
  intro x y eq
  have value (off : Nat) (ho : off≤8) :
      (slot 0x700800 i (BitVec.ofNat 32 off)+BitVec.ofNat 32 x.val).toNat=0x700800+12*i+off+x.val := by
    change (BitVec.ofNat 32 0x700800+BitVec.ofNat 32 (12*i)+BitVec.ofNat 32 off+BitVec.ofNat 32 x.val).toNat=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have hx := x.isLt
    omega
  have right : (a+BitVec.ofNat 32 y.val).toNat=a.toNat+y.val := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have hy:=y.isLt; omega),Nat.mod_eq_of_lt (by have hy:=y.isLt; omega)]
  have num := congrArg BitVec.toNat eq
  rw [right] at num
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl
  all_goals
    try simp only [show (4 : Word)=(4#32) by decide,show (8 : Word)=(8#32) by decide] at num
    rw [value _ (by decide)] at num
    have hy := y.isLt
    omega


theorem fixedSlotSafe (a : Word) (ha : a∈protectedWords) : ArraySafe 0x700800 a := by
  constructor
  · intro k hk off ho
    apply FloorCaller.apart_symm (below_storage k hk off ho a ?_)
    simp only [protectedWords,OriginalLineSecondPoint.reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · simp only [protectedWords,OriginalLineSecondPoint.reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem layout (wide : Mode) : OriginalLineCollection.Layout (iterator wide) 0x700800 := by
  constructor
  · intro k hk off ho
    constructor
    · apply below_storage k hk off ho
      cases wide <;> decide
    · apply below_storage k hk off ho
      cases wide <;> decide
  · intro k hk off ho j hj
    change Apart (slot 0x700800 k off) ((OriginalLineDispatch.view (atIndex (iterator wide) 0)).regs 4-j)
    rw [indexedStack wide 0]
    apply below_storage k hk off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk off ho j hj
    change Apart (slot 0x700800 k off) ((OriginalLineDispatch.view (atIndex (iterator wide) 0)).regs 4-(36#32)+j)
    rw [indexedStack wide 0]
    apply below_storage k hk off ho
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk off ho; exact below_storage k hk off ho _ (by decide)

theorem atZero (wide : Mode) : atIndex (iterator wide) 0=iterator wide := by
  unfold atIndex OriginalLineInvariant.atIndex OriginalLineInvariant.address
  simp only [Nat.mul_zero,BitVec.add_zero]
  apply congrArg (fun regs => X86Memory.State.mk regs (iterator wide).memory)
  funext reg
  simp only [write]
  split <;> simp_all [iterator]

def plan (wide : Mode) : Initial (iterator wide) 1 0x700800 resolve := by
  refine ⟨fun _ => candidate wide,protectedWords,?_,?_,?_,?_,?_,?_,?_,?_,?_,fixedSlotSafe,?_,?_,?_,?_⟩
  · intro i hi
    have indices : i=0 ∨ i=1 := by omega
    rcases indices with rfl|rfl <;> cases wide <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> cases wide <;> decide
  · cases wide <;> decide
  · intro i hi
    have eq : i=0 := by omega
    subst i
    cases wide <;> decide
  · intro i hi a ha
    simp only [Candidate.reads,candidate] at ha
    simp only [OriginalLineSecondPoint.reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi no
    simp [candidate] at no
  · intro i hi yes
    have eq : i=0 := by omega
    subst i
    rw [atZero]
    refine ⟨inputs wide,?_,?_,?_⟩
    · cases wide <;> rfl
    · cases wide <;> decide
    · cases wide <;> decide
  · intro i hi yes
    rfl
  · intro i hi a ha
    have eq : i=0 := by omega
    subst i
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · apply wordWrites a ha; cases wide <;> decide
    · apply wordWrites a ha; cases wide <;> decide
    · intro off ho
      rw [indexedStack wide 0]
      apply wordWrites a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    · intro off ho
      rw [indexedStack wide 0]
      apply wordWrites a ha
      simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi
    have eq : i=0 := by omega
    subst i
    refine ⟨?_,?_,?_⟩
    · cases wide <;> constructor <;> unfold Apart <;> decide
    · intro off ho
      rw [indexedStack wide 0]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    · intro off ho
      rw [indexedStack wide 0]
      simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    all_goals
      constructor
      · intro k hk off ho; exact FloorCaller.apart_symm (below_storage k hk off ho _ (by cases wide <;> decide))
      · cases wide <;> unfold Apart <;> decide
  · intro i hi
    have eq : i=0 := by omega
    subst i
    cases wide <;> unfold Apart <;> decide
  · intro i hi
    have eq : i=0 := by omega
    subst i
    rw [atZero]
    exact layout wide

theorem tracked (wide : Mode) : Tracks (iterator wide) 0x700800 resolve (collected wide).collected 1 := by
  constructor
  · intro i hi
    have eq : i=0 := by simpa [collected] using hi
    subst i
    cases wide <;> constructor <;> try decide
    all_goals constructor <;> decide +revert
  · cases wide <;> decide
  · cases wide <;> decide

def out (wide : Mode) := scan (plan wide).candidates 1 0 ⟨iterator wide,none,0x2c57f⟩ (collected wide)

theorem stopChecked (wide : Mode) (stops : wide≠.negative) :
    Terminal (iterator wide) (plan wide) 1 (out wide).machine (out wide).path ∧
    OriginalLineTraversal.Runs ⟨iterator wide,none,0x2c57f⟩ (out wide).machine 1 := by
  have result := stopping_prefix (iterator wide) 1 0x700800 resolve (plan wide) (collected wide) none (tracked wide)
    (by cases wide <;> first | contradiction | decide)
  have count : (out wide).visits=1 := by cases wide <;> decide
  have checked := result.2.2
  change Terminal (iterator wide) (plan wide) (out wide).visits (out wide).machine (out wide).path ∧
    OriginalLineTraversal.Runs ⟨iterator wide,none,0x2c57f⟩ (out wide).machine (out wide).visits at checked
  simpa only [count] using checked

example : load16 (iterator .shortStop).memory (address (iterator .shortStop) 1)≠(0xffff#16) := by decide
example : (out .shortStop).path.completed=false := (stopChecked .shortStop (by decide)).1.completed
example : (out .wideStop).machine.core.regs 0=(0#32) := (stopChecked .wideStop (by decide)).1.value
example : (out .wideStop).path.collected.size=1 := by decide
example : load32 (out .shortStop).machine.core.memory (0x2c028#32)=(0x70080c#32) := by decide
example : (out .shortStop).machine.pc=0x4f000 := by decide
example : (out .negative).stopped=false := by decide
example : (out .negative).path.collected.size=1 := by decide
example : Collision.lineIntercept (ray .negative false) wall=.ok none := by rfl
example : ∃ steps≤288, X86Routine.Prefix OriginalLineMixedInvariant.program [] steps
    ⟨iterator .negative,none,0x2c57f⟩
    (complete (plan .negative).candidates 1 ⟨iterator .negative,none,0x2c57f⟩ (collected .negative)).machine :=
  (through_scan (iterator .negative) 1 0x700800 resolve (plan .negative) (collected .negative) none
    (tracked .negative) (by decide)).2.1
-- A previously stamped line must be skipped even if its geometry could stop.
example : (scan (fun _ => candidate .shortStop) 1 0
    ⟨{iterator .shortStop with memory:=store32 (iterator .shortStop).memory (0x600236#32) (99#32)},none,0x2c57f⟩
    (collected .shortStop)).stopped=false := by decide
end LineScanFixtures

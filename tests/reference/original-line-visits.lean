import Doom.Proofs.OriginalLineVisits
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineSecondPoint
namespace LineMixedInvariantFixtures
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (wide same : Bool) : Collision.Divline :=
  if wide then ⟨⟨-65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
  else ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def mem (wide same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x60023e,0x600420),(0x600242,0x600430),(0x600246,0),(0x60024a,65536),
   (0x600420,4194304),(0x600424,131072),(0x600430,4194304),(0x600434,196608),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray wide same).x.raw.toBitVec),(0x2ba14,(ray wide same).y.raw.toBitVec),
   (0x2ba18,(ray wide same).dx.raw.toBitVec),(0x2ba1c,(ray wide same).dy.raw.toBitVec),
   (0x600100,0xdeadbeef),(0x600104,0x2c5f0),(0x600108,777),(0x60010c,0x4f000),(0x13580,99),(0x2c120,0x600200),(0x600900,0),(0x600904,0xffff0001),(0x600110,111),(0x600114,222),(0x600118,333),(0x60011c,444),
   (0x600120,555),(0x600124,0x4f000),(0x2c028,0x70080c),(0x700800,123),(0x700804,1),(0x700808,0x600500)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def fixture (wide same : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then OriginalLineSide.bit (firstSide (ray wide same) wall)
    else if r=1 then 0x600200 else if r=4 then 0x600100 else BitVec.ofNat 32 (r.val*11),mem wide same⟩


def iterator (wide : Bool) : X86Memory.State :=
  ⟨fun r => if r=2 then 0x600900 else if r=4 then 0x600104 else 0,mem wide false⟩
def callback (wide : Bool) := OriginalLineDispatch.view (iterator wide)
def fraction (wide : Bool) : Fixed := if wide then ⟨2048⟩ else ⟨43690⟩

theorem inputs (wide : Bool) : OriginalLineCrossing.Inputs (callback wide) (ray wide false) wall 0x600200 0x600400 0x600410 := by
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

theorem scratch (wide : Bool) (a : Word)
    (ha : a∈[(0x600200#32),0x600208,0x60020c,0x600400,0x600404,0x2ba10,0x2ba14,0x2ba18,0x2ba1c,0x2c024,0x600232,0x2c028]) :
    OriginalLineCrossing.ScratchSafe (callback wide) a := by
  intro off ho
  change Apart a ((OriginalLineDispatch.entry (iterator wide)).core.regs 4-(36#32)+off)
  rw [(OriginalLineDispatch.entry_regs (iterator wide)).2.2]
  have sp : (iterator wide).regs 4-(4#32)=(0x600100#32) := by cases wide <;> decide
  rw [sp]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem sides (wide : Bool) (a : Word) (ha : a∈[(0x2c024#32),0x600232,0x2c028]) :
    OriginalLineCrossing.SideSafe (callback wide) a := by
  intro off ho
  change Apart a ((OriginalLineDispatch.entry (iterator wide)).core.regs 4-off)
  rw [(OriginalLineDispatch.entry_regs (iterator wide)).2.2]
  have sp : (iterator wide).regs 4-(4#32)=(0x600100#32) := by cases wide <;> decide
  rw [sp]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem tail (wide : Bool) : OriginalLineDispatch.TailData (iterator wide) (ray wide false) wall (fraction wide) 0 0x600200 0x600400 := by
  constructor
  · cases wide <;> rfl
  · intro a ha
    apply scratch
    simp only [OriginalLineFraction.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · cases wide <;> decide
  · cases wide <;> decide
  · exact ⟨sides wide _ (by simp),scratch wide _ (by simp)⟩
  · exact ⟨sides wide _ (by simp),scratch wide _ (by simp)⟩
  · exact ⟨sides wide _ (by simp),scratch wide _ (by simp)⟩
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> cases wide <;> unfold Apart <;> decide

  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> cases wide <;> constructor <;> unfold Apart <;> decide

theorem fresh (wide : Bool) : OriginalLineDispatch.Fresh (iterator wide) := by
  cases wide <;> constructor <;> try decide
  all_goals unfold Apart; decide

theorem ready (wide : Bool) : OriginalLineDispatch.Ready (iterator wide) (ray wide false) wall (fraction wide) 0 0x600200 0x600400 0x600410 := by
  refine ⟨fresh wide,inputs wide,?_,tail wide⟩
  intro a ha
  simp only [OriginalLineSecondPoint.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases wide <;> constructor <;> unfold Apart <;> decide

open OriginalLineCollection

def oldHit : Collision.Intercept := ⟨⟨123⟩,true,17⟩
def resolve (hit : Collision.Intercept) : Word := if hit.id=17 then 0x600500 else 0x600200
def collected (wide : Bool) : Collision.PathResult := { trace:=ray wide false, collected:=#[oldHit] }

open OriginalLineMixedInvariant

def farWall : Collision.Line := { wall with x:=⟨4194304⟩,y:=⟨131072⟩ }
def candidate (wide : Bool) (i : Nat) : Candidate :=
  if i=2 then ⟨ray wide false,farWall,0x60023e,0x600420,0x600430,⟨0⟩,0,1,false⟩
  else ⟨ray wide false,wall,0x600200,0x600400,0x600410,fraction wide,0,0,true⟩
def protectedWords : List Word :=
  OriginalLineSecondPoint.reads 0x600200 0x600400 0x600410 ++
  OriginalLineSecondPoint.reads 0x60023e 0x600420 0x600430 ++
  [0x600232,0x600270,0x2c024,0x600104,0x13580,0x2c120,0x600900,0x600902,0x600904,0x600906,0x600108,0x60010c]

theorem rejectedInputs (wide : Bool) : OriginalLineReject.Inputs
    (OriginalLineDispatch.view (OriginalLineInvariant.atIndex (iterator wide) 2))
    (ray wide false) farWall 0x60023e 0x600420 0x600430 := by
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


theorem indexedStack (wide : Bool) (i : Nat) :
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

theorem initialStorage (wide : Bool) (i : Nat) (hi : i<3) :
    OriginalLineCollection.Layout (atIndex (iterator wide) i) 0x700800 := by
  have indices : i=0 ∨ i=1 ∨ i=2 := by omega
  have stamp : (OriginalLineDispatch.stamp (atIndex (iterator wide) i)).toNat≤0x7007fc := by
    rcases indices with rfl|rfl|rfl <;> cases wide <;> decide
  have stack : (atIndex (iterator wide) i).regs 4=(0x600104#32) := rfl
  constructor
  · intro k hk off ho
    constructor
    · exact below_storage k hk off ho _ stamp
    · rw [stack]; exact below_storage k hk off ho _ (by decide)
  · intro k hk off ho j hj
    rw [indexedStack wide i]
    apply below_storage k hk off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk off ho j hj
    rw [indexedStack wide i]
    apply below_storage k hk off ho
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk off ho; exact below_storage k hk off ho _ (by decide)

def plan (wide : Bool) : Initial (iterator wide) 3 0x700800 resolve := by
  refine ⟨candidate wide,protectedWords,?_,?_,?_,?_,?_,?_,?_,?_,?_,fixedSlotSafe,?_,?_,?_,initialStorage wide⟩
  · intro i hi
    have indices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases indices with rfl|rfl|rfl|rfl <;> cases wide <;> decide
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> cases wide <;> decide
  · cases wide <;> decide
  · intro i hi
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases indices with rfl|rfl|rfl <;> cases wide <;> decide
  · intro i hi a ha
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases indices with rfl|rfl|rfl
    all_goals
      simp only [Candidate.reads,candidate,ite_true,show ¬(0 : Nat)=2 by decide,show ¬(1 : Nat)=2 by decide,ite_false] at ha
      simp only [OriginalLineSecondPoint.reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi no
    have eq : i=2 := by
      by_cases eq : i=2
      · exact eq
      · simp [candidate,eq] at no
    subst i
    exact rejectedInputs wide
  · intro i hi yes
    have ne : i≠2 := by intro eq; subst i; simp [candidate] at yes
    have indices : i=0 ∨ i=1 := by omega
    have geometry : OriginalLineCrossing.Inputs (OriginalLineDispatch.view (atIndex (iterator wide) i))
        (ray wide false) wall 0x600200 0x600400 0x600410 := by
      apply crossing_inputs (callback wide) _ _ _ _ _ _ (inputs wide)
      · change (OriginalLineDispatch.entry (atIndex (iterator wide) i)).core.regs 0=(OriginalLineDispatch.entry (iterator wide)).core.regs 0
        rw [(OriginalLineDispatch.entry_regs _).1,(OriginalLineDispatch.entry_regs _).1]
        rcases indices with rfl|rfl <;> cases wide <;> decide
      · rw [indexedStack wide i]
        exact (indexedStack wide 0).symm
      · intro a ha; rfl
    simp only [candidate,if_neg ne]
    exact ⟨geometry,(tail wide).computed,(tail wide).active,(tail wide).back⟩
  · intro i hi yes
    have ne : i≠2 := by intro eq; subst i; simp [candidate] at yes
    simp [candidate,ne,Candidate.hit,resolve]
  · intro i hi a ha
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · rcases indices with rfl|rfl|rfl
      all_goals
        apply wordWrites a ha
        cases wide <;> decide
    · exact wordWrites a ha _ (by change (0x600104#32)-(4#32)∈writes; decide)
    · intro off ho
      rw [indexedStack wide i]
      apply wordWrites a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    · intro off ho
      rw [indexedStack wide i]
      apply wordWrites a ha
      simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    refine ⟨?_,?_,?_⟩
    · rcases indices with rfl|rfl|rfl <;> cases wide <;> constructor <;> unfold Apart <;> decide
    · intro off ho
      rw [indexedStack wide i]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
    · intro off ho
      rw [indexedStack wide i]
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
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases indices with rfl|rfl|rfl <;> cases wide <;> unfold Apart <;> decide

theorem tracked (wide : Bool) : Tracks (iterator wide) 0x700800 resolve (collected wide).collected 3 := by
  constructor
  · intro i hi
    have eq : i=0 := by simpa [collected] using hi
    subst i
    cases wide <;> constructor <;> try decide
    all_goals constructor <;> decide +revert
  · cases wide <;> decide
  · cases wide <;> decide


theorem keeps (wide : Bool) : ∀ j<3, ((plan wide).candidates j).crosses=true → ((plan wide).candidates j).Continues := by
  intro j hj yes
  have indices : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases indices with rfl|rfl|rfl <;> cases wide <;> right <;> decide

theorem sentinel (wide : Bool) : load16 (iterator wide).memory (address (iterator wide) 3)=(0xffff#16) := by
  cases wide <;> decide

def out (wide : Bool) := finished (iterator wide) 3 0x700800 resolve (plan wide) none (collected wide)
example (wide : Bool) : ∃ steps≤850, X86Routine.Prefix OriginalLineMixedInvariant.program [] steps
    ⟨iterator wide,none,0x2c57f⟩ (out wide).1 :=
  (through_sentinel (iterator wide) 3 0x700800 resolve (plan wide) (collected wide) none (tracked wide) (keeps wide) (sentinel wide)).1
example (wide : Bool) : OriginalLineTraversal.Runs ⟨iterator wide,none,0x2c57f⟩ (out wide).1 3 :=
  (through_sentinel (iterator wide) 3 0x700800 resolve (plan wide) (collected wide) none (tracked wide) (keeps wide) (sentinel wide)).2.1
example (wide : Bool) : Tracks (out wide).1.core 0x700800 resolve (out wide).2.collected 0 :=
  (through_sentinel (iterator wide) 3 0x700800 resolve (plan wide) (collected wide) none (tracked wide) (keeps wide) (sentinel wide)).2.2.1
example (wide : Bool) : (out wide).1.pc=0x4f000 := by
  have ret := parent_return (iterator wide) 3 0x700800 resolve (plan wide) (collected wide) none (tracked wide) (keeps wide)
    (by cases wide <;> decide) (by cases wide <;> decide)
  exact ret.2.2.2.trans (by cases wide <;> decide)
example : (out false).2.collected.size=2 := by decide
example : (out true).2.collected[0]!.id=17 := by decide
example : (out true).2.collected[1]!.id=0 := by decide
example : load32 (out false).1.core.memory (0x2c028#32)=(0x700818#32) := by decide
example : load32 (out false).1.core.memory (0x600274#32)=(99#32) := by decide
end LineMixedInvariantFixtures

namespace LineMixedInvariantFixtures
open OriginalLineVisits OriginalLineMixedInvariant
set_option backward.isDefEq.respectTransparency false

theorem visitLayout (wide : Bool) : OriginalLineVisits.Layout (iterator wide) (plan wide) 0x600200 2 := by
  refine ⟨by decide,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases indices with rfl|rfl|rfl <;> cases wide <;> decide
  · intro i hi
    have indices : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases indices with rfl|rfl|rfl <;> cases wide <;> decide
  · intro j hj
    have indices : j=0 ∨ j=1 := by omega
    rcases indices with rfl|rfl <;> cases wide <;> unfold Apart <;> decide
  · intro i hi j hj off ho
    change Apart _ ((OriginalLineDispatch.entry (atIndex (iterator wide) i)).core.regs 4-off)
    rw [(OriginalLineDispatch.entry_regs _).2.2]
    change Apart (stamp 0x600200 j) ((iterator wide).regs 4-(4#32)-off)
    have indices : j=0 ∨ j=1 := by omega
    rcases indices with rfl|rfl
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    all_goals rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases wide <;> unfold Apart <;> decide
  · intro i hi j hj off ho
    change Apart _ ((OriginalLineDispatch.entry (atIndex (iterator wide) i)).core.regs 4-(36#32)+off)
    rw [(OriginalLineDispatch.entry_regs _).2.2]
    change Apart (stamp 0x600200 j) ((iterator wide).regs 4-(4#32)-(36#32)+off)
    have indices : j=0 ∨ j=1 := by omega
    rcases indices with rfl|rfl
    all_goals simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
    all_goals rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases wide <;> unfold Apart <;> decide
  · intro j hj
    have indices : j=0 ∨ j=1 := by omega
    rcases indices with rfl|rfl
    all_goals constructor
    all_goals first
      | (intro k hk off ho; exact FloorCaller.apart_symm (below_storage k hk off ho _ (by decide)))
      | (unfold Apart; decide)

theorem initialSeen (wide : Bool) : Represents (iterator wide).memory 0x600200 99 #[false,false] := by
  constructor
  · cases wide <;> decide
  · intro j hj
    have indices : j=0 ∨ j=1 := by change j<2 at hj; omega
    rcases indices with rfl|rfl <;> cases wide <;> decide

def visitOut (wide : Bool) := OriginalLineScan.scan (plan wide).candidates 3 0
  ⟨iterator wide,none,0x2c57f⟩ (collected wide)

theorem visitExecution (wide : Bool) :
    (∃ steps≤281*3, X86Routine.Prefix OriginalLineMixedInvariant.program [] steps
      ⟨iterator wide,none,0x2c57f⟩ (visitOut wide).machine) ∧
    Represents (visitOut wide).machine.core.memory 0x600200 99 #[true,true] := by
  have run := OriginalLineVisits.scan_execution (iterator wide) 3 0x700800 resolve (plan wide)
    0x600200 2 (visitLayout wide) none (collected wide) (tracked wide) 99 #[false,false] rfl (initialSeen wide)
  have visits : (visitOut wide).visits=3 := by cases wide <;> decide
  have rel := run.2.2
  change Represents (visitOut wide).machine.core.memory 0x600200 99
    (markPrefix (plan wide).candidates (visitOut wide).visits 0 #[false,false]) at rel
  rw [visits] at rel
  have bits : markPrefix (plan wide).candidates 3 0 #[false,false]=#[true,true] := by cases wide <;> decide
  rw [bits] at rel
  refine ⟨?_,rel⟩
  have path := run.2.1
  change ∃ steps≤281*(visitOut wide).visits, _ at path
  rw [visits] at path
  exact path

#print axioms visitLayout
#print axioms visitExecution
end LineMixedInvariantFixtures

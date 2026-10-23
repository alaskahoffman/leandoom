import Doom.Proofs.OriginalLineCollection
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineSecondPoint
namespace LineCollectionFixtures
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (wide same : Bool) : Collision.Divline :=
  if wide then ⟨⟨-65536⟩,⟨if same then 131072 else 32768⟩,⟨2097152⟩,⟨0⟩⟩
  else ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def mem (wide same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray wide same).x.raw.toBitVec),(0x2ba14,(ray wide same).y.raw.toBitVec),
   (0x2ba18,(ray wide same).dx.raw.toBitVec),(0x2ba1c,(ray wide same).dy.raw.toBitVec),
   (0x600100,0xdeadbeef),(0x600104,0x2c5f0),(0x600108,777),(0x60010c,0x4f000),(0x13580,99),(0x2c120,0x600200),(0x600900,0),(0x600904,0xffff),(0x600110,111),(0x600114,222),(0x600118,333),(0x60011c,444),
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

theorem tracked (wide : Bool) : Tracks (iterator wide) 0x700800 resolve (collected wide).collected 2 := by
  constructor
  · intro i hi
    have eq : i=0 := by simpa [collected] using hi
    subst i
    cases wide <;> constructor <;> try decide
    all_goals constructor <;> decide +revert
  · cases wide <;> decide
  · cases wide <;> decide

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

theorem layout (wide : Bool) : Layout (iterator wide) 0x700800 := by
  have stamp : OriginalLineDispatch.stamp (iterator wide)=(0x600236#32) := by cases wide <;> decide
  have stack : (iterator wide).regs 4=(0x600104#32) := rfl
  have sp : (callback wide).regs 4=(0x600100#32) :=
    (OriginalLineDispatch.entry_regs _).2.2.trans (by rw [stack]; decide)
  constructor
  · intro i hi off ho
    simp only [OriginalLineDispatch.Safe,stamp,stack]
    constructor <;> apply below_storage i hi off ho <;> decide
  · intro i hi off ho k hk
    change Apart _ ((callback wide).regs 4-k)
    rw [sp]
    apply below_storage i hi off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi off ho k hk
    change Apart _ ((callback wide).regs 4-(36#32)+k)
    rw [sp]
    apply below_storage i hi off ho
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro i hi off ho
    exact below_storage i hi off ho _ (by decide)

def next (wide : Bool) := OriginalLineDispatch.result (iterator wide)
def hits (wide : Bool) := (collected wide).collected.push ⟨fraction wide,true,0⟩

theorem appended (wide : Bool) : Tracks (next wide).core 0x700800 resolve (hits wide) 1 :=
  (OriginalLineCollection.append (iterator wide) (ray wide false) wall (fraction wide) 0
    0x600200 0x600400 0x600410 (ready wide) (collected wide) 0 0x700800 resolve 1
    (tracked wide) (layout wide) (by cases wide <;> decide) (by cases wide <;> decide) (by rfl)).2

example (wide : Bool) : ∃ steps≤281, X86Routine.Prefix OriginalLineDispatch.program [] steps
    ⟨iterator wide,none,0x2c57f⟩ (next wide) := by
  have path := OriginalLineCollection.append_execution (iterator wide) none (ray wide false) wall (fraction wide) 0
    0x600200 0x600400 0x600410 (ready wide) (collected wide) 0 0x700800 resolve 1
    (tracked wide) (layout wide) (by cases wide <;> decide) (by cases wide <;> decide) (by rfl) ?_
  · exact path.1
  · intro addr ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> cases wide <;> unfold Apart <;> decide

example (wide : Bool) : Tracks (OriginalLineCell.visit (next wide).core).core 0x700800 resolve (hits wide) 0 :=
  OriginalLineCollection.duplicate (next wide).core 0x700800 resolve (hits wide) 0
    (appended wide) (by cases wide <;> decide) (by cases wide <;> decide)
example (wide : Bool) : load32 (next wide).core.memory (0x700800#32)=(123#32) := by
  have old := (appended wide).encoded 0 (by simp [hits,collected])
  exact old.1
example (wide : Bool) : load32 (next wide).core.memory (0x70080c#32)=(fraction wide).raw.toBitVec := by
  have last := (appended wide).encoded 1 (by simp [hits,collected])
  exact last.1
example (wide : Bool) : load32 (next wide).core.memory (0x2c028#32)=(0x700818#32) :=
  (appended wide).cursor
example : Apart ((0xfffffff8#32)+BitVec.ofNat 32 (12*0)+(8#32))
    ((0xfffffff8#32)+BitVec.ofNat 32 (12*127)+(0#32)) :=
  slots_apart _ 0 127 (by decide) (by decide) (by decide) _ _ (by simp) (by simp)
end LineCollectionFixtures

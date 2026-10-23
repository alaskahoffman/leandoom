import Doom.Proofs.E1M1ScanGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry OriginalLineMixedInvariant
namespace ScanGeometryFixture
-- Diagnostic states, not a claim of reachability from the E1M1 start.
-- Original SP=1 deliberately exercises modular stack arithmetic.
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (same : Bool) : Collision.Divline :=
  ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def memory (same : Bool) : Memory :=
  [(0x600200,0x600400),(0x600204,0x600410),(0x600208,0),(0x60020c,65536),
   (0x600400,0),(0x600404,0),(0x600410,0),(0x600414,65536),
   (0x2ba10,(ray same).x.raw.toBitVec),(0x2ba14,(ray same).y.raw.toBitVec),
   (0x2ba18,(ray same).dx.raw.toBitVec),(0x2ba1c,(ray same).dy.raw.toBitVec),
   (0x2c120,0x600200),(0x600900,0)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)
def scan (same : Bool) : X86Memory.State :=
  ⟨fun r => if r=2 then 0x600900 else if r=4 then (1#32)-124 else 0,memory same⟩

theorem geometry (same : Bool) :
    Geometry (OriginalLineDispatch.view (atIndex (scan same) 0)) (ray same) wall 0x600200 0x600400 0x600410 := by
  apply callback_geometry (scan same) 1 (by rfl) 0 (ray same) wall
  · cases same <;> decide
  · cases same <;> decide
  · cases same <;> constructor <;> decide
  · intro a ha off ho
    simp only [OriginalLineSecondPoint.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

example : OriginalLineCrossing.Inputs (OriginalLineDispatch.view (atIndex (scan false) 0))
    (ray false) wall 0x600200 0x600400 0x600410 :=
  crossing_inputs _ _ _ _ _ _ (geometry false) (by decide)
example : OriginalLineReject.Inputs (OriginalLineDispatch.view (atIndex (scan true) 0))
    (ray true) wall 0x600200 0x600400 0x600410 :=
  rejection_inputs _ _ _ _ _ _ (geometry true) (by decide)
example : (OriginalLineDispatch.view (atIndex (scan false) 0)).regs 4=0xffffff81 :=
  view_stack (scan false) 1 rfl 0

-- Quantify over every record and byte, rather than enumerating 128*475 pairs.
theorem record_apart (k : Nat) (hk : k<128) (off : Word) (ho : off∈[(0#32),4,8])
    (a : Word) (lo : 0x2c020≤a.toNat) (hi : a.toNat≤0xfffffffc) :
    Apart (OriginalLineCollection.slot 0x2ba20 k off) a := by
  intro x y eq
  have value (off : Nat) (ho : off≤8) :
      (OriginalLineCollection.slot 0x2ba20 k (BitVec.ofNat 32 off)+BitVec.ofNat 32 x.val).toNat=0x2ba20+12*k+off+x.val := by
    change (BitVec.ofNat 32 0x2ba20+BitVec.ofNat 32 (12*k)+BitVec.ofNat 32 off+BitVec.ofNat 32 x.val).toNat=_
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
    have hx := x.isLt
    omega

theorem storage : Storage 1 0x600200 := by
  constructor
  · intro k hk off ho id bound
    have stampValue : (OriginalLineVisits.stamp 0x600200 id).toNat=id*62+0x600200+54 := by
      change ((BitVec.ofNat 32 id * BitVec.ofNat 32 62)+BitVec.ofNat 32 0x600200+BitVec.ofNat 32 54).toNat=_
      rw [←BitVec.ofNat_mul,←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      omega
    apply record_apart k hk off ho <;> rw [stampValue] <;> omega
  · intro k hk off ho
    exact record_apart k hk off ho _ (by decide) (by decide)
  · intro k hk off ho d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact record_apart k hk off ho _ (by decide) (by decide)
  · intro k hk off ho d hd
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact record_apart k hk off ho _ (by decide) (by decide)
  · intro k hk off ho
    exact record_apart k hk off ho _ (by decide) (by decide)

example (same : Bool) : OriginalLineCollection.Layout (atIndex (scan same) 0) 0x2ba20 :=
  storage_layout (scan same) 1 0x600200 rfl 0 0 (by decide)
    (by cases same <;> decide) storage

-- The last byte of the last record belongs to storage: adjacent-word aliasing
-- must be rejected too, not just equality of starting addresses.
example : ¬Apart (OriginalLineCollection.slot 0x2ba20 127 8) (0x2c01d#32) := by unfold Apart; decide
example : ¬SideSafe 1 (0xffffff7e#32) := by
  intro safe
  exact safe (4#32) (by simp) ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide)
#print axioms geometry
#print axioms storage
end ScanGeometryFixture

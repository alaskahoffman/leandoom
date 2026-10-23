import Doom.Proofs.E1M1ScanContracts
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry OriginalLineMixedInvariant
namespace ScanContractsFixture
-- Diagnostic states, not a claim of reachability from the E1M1 start.
-- Original SP=1 deliberately exercises modular stack arithmetic.
def wall : Collision.Line := { (default : Collision.Line) with x:=⟨0⟩,y:=⟨0⟩,dx:=⟨0⟩,dy:=⟨65536⟩ }
def ray (same : Bool) : Collision.Divline :=
  ⟨⟨-131072⟩,⟨32768⟩,⟨if same then 65536 else 196608⟩,⟨0⟩⟩
def memory (same : Bool) : Memory :=
  [(0x600200,0x700400),(0x600204,0x700410),(0x600208,0),(0x60020c,65536),
   (0x700400,0),(0x700404,0),(0x700410,0),(0x700414,65536),
   (0x2ba10,(ray same).x.raw.toBitVec),(0x2ba14,(ray same).y.raw.toBitVec),
   (0x2ba18,(ray same).dx.raw.toBitVec),(0x2ba1c,(ray same).dy.raw.toBitVec),
   (0x2c120,0x600200),(0x800900,0),(0x800904,65535),(0x13580,99),(0xffffff85,0x2c5f0),(0x2c028,0x2ba20)].foldl (fun m (a,v) => store32 m a v) (fun _ => 0)
def scan (same : Bool) : X86Memory.State :=
  ⟨fun r => if r=2 then 0x800900 else if r=4 then (1#32)-124 else 0,memory same⟩

theorem geometry (same : Bool) :
    Geometry (OriginalLineDispatch.view (atIndex (scan same) 0)) (ray same) wall 0x600200 0x700400 0x700410 := by
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
    (ray false) wall 0x600200 0x700400 0x700410 :=
  crossing_inputs _ _ _ _ _ _ (geometry false) (by decide)
example : OriginalLineReject.Inputs (OriginalLineDispatch.view (atIndex (scan true) 0))
    (ray true) wall 0x600200 0x700400 0x700410 :=
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


open E1M1ScanContracts

abbrev cell : E1M1PathMap.Cell := ⟨0,[0,0]⟩
abbrev data (_ : Nat) : E1M1ScanContracts.LineData := ⟨wall,0x700400,0x700410,⟨43690⟩⟩
def cs (same : Bool) := candidates (ray same) 0x600200 cell.ids data

theorem word_stamp_safe (a : Word)
    (ha : a∈[(0xffffff85#32),0x13580,0x2c120,0x800900,0x800902,0x800904,
      0x600200,0x600204,0x600208,0x60020c,0x700400,0x700404,0x700410,0x700414,
      0x2ba10,0x2ba14,0x2ba18,0x2ba1c,0x600232,0x2c024,0x2c028,0xffffff81])
    (id : Nat) (bound : id<475) : Apart a (OriginalLineVisits.stamp 0x600200 id) := by
  intro x y eq
  have right : (OriginalLineVisits.stamp 0x600200 id+BitVec.ofNat 32 y.val).toNat=0x600200+62*id+54+y.val := by
    change ((BitVec.ofNat 32 id*BitVec.ofNat 32 62)+BitVec.ofNat 32 0x600200+BitVec.ofNat 32 54+BitVec.ofNat 32 y.val).toNat=_
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    · omega
    · have hy := y.isLt; omega
  have num := congrArg BitVec.toNat eq
  rw [right] at num
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at num
    dsimp at num
    have hx := x.isLt
    have hy := y.isLt
    omega

def reads : List Word := [0xffffff85,0x13580,0x2c120,0x800900,0x800902,0x800904,
      0x600200,0x600204,0x600208,0x60020c,0x700400,0x700404,0x700410,0x700414,
      0x2ba10,0x2ba14,0x2ba18,0x2ba1c,0x600232,0x2c024]

theorem members (same : Bool) (a : Word) (ha : a∈protectedWords 1 0x800900 2 (cs same)) : a∈reads := by
  simpa [protectedWords,cs,candidates,candidate,cell,data,Candidate.reads,OriginalLineSecondPoint.reads,linePointer,
    List.range_succ,reads,or_assoc,or_left_comm,or_comm] using ha

theorem word_protected (a : Word) (ha : a∈reads++[0x2c028]) : E1M1ScanContracts.Protected 1 0x600200 a := by
  constructor
  · exact word_stamp_safe a (by simpa [reads] using List.mem_append_left [0xffffff81] ha)
  ·
    simp only [reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  · intro off ho
    simp only [reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  · intro off ho
    simp only [reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

-- Read words below the array need the opposite interval bound from record_apart.
theorem below_records (a : Word) (ha : a.toNat≤0x2ba1c) (k : Nat) (hk : k<128)
    (off : Word) (ho : off∈[(0#32),4,8]) : Apart a (OriginalLineCollection.slot (0x2ba20#32) k off) := by
  intro x y eq
  have right (off : Nat) (ho : off≤8) :
      (OriginalLineCollection.slot (0x2ba20#32) k (BitVec.ofNat 32 off)+BitVec.ofNat 32 y.val).toNat=0x2ba20+12*k+off+y.val := by
    change (BitVec.ofNat 32 0x2ba20+BitVec.ofNat 32 (12*k)+BitVec.ofNat 32 off+BitVec.ofNat 32 y.val).toNat=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have hy:=y.isLt; omega
  have left : (a+BitVec.ofNat 32 x.val).toNat=a.toNat+x.val := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have hx:=x.isLt; omega),Nat.mod_eq_of_lt (by have hx:=x.isLt; omega)]
  have num := congrArg BitVec.toNat eq
  rw [left] at num
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl
  all_goals
    try simp only [BitVec.ofNat_eq_ofNat] at num
    rw [right _ (by decide)] at num
    have hx:=x.isLt
    omega

theorem array_safe (a : Word) (ha : a∈reads++[0xffffff81,0xffffff75]) : ArraySafe 0x2ba20 a := by
  constructor
  · intro k hk off ho
    simp only [reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact FloorCaller.apart_symm (record_apart k hk off ho _ (by decide) (by decide))
      | exact below_records _ (by decide) k hk off ho
  · simp only [reads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem layout (same : Bool) : E1M1ScanContracts.Layout 1 0x800900 0x600200 2 (cs same) := by
  refine ⟨fun a ha => word_protected a (List.mem_append_left _ (members same a ha)),
    fun a ha => array_safe a (List.mem_append_left _ (members same a ha)),
    word_protected _ (by simp),?_,?_,storage⟩
  · intro a ha
    apply array_safe a
    exact List.mem_append_right _ ha
  · intro id bound
    -- The wrapped stack is above every bounded stamp.
    exact FloorCaller.apart_symm (word_stamp_safe 0xffffff81 (by simp) id bound)


theorem list_items (same : Bool) : ∀ i : Fin 2, OriginalLineCell.itemWord (atIndex (scan same) i.val)=0 := by
  cases same <;> decide

theorem items (same : Bool) : E1M1PathMapLookup.ScanWords (scan same) 0x600200 cell := by
  have zeros : ∀ i : Fin 2, cell.ids[i.val]=0 := by decide
  have base : load32 (scan same).memory (0x2c120#32)=(0x600200#32) := by cases same <;> decide
  constructor
  · intro i
    rw [zeros i]
    exact list_items same i
  · intro i
    rw [list_items same i]
    decide
  · intro i frac
    unfold OriginalLineDispatch.pointer
    rw [list_items same i]
    change (0#32)*(62#32)+load32 (scan same).memory (0x2c120#32)=_
    rw [base]
    simp [E1M1PathMap.resolve,zeros i]
  · cases same <;> decide

theorem ids : ∀ i : Fin cell.ids.length, cell.ids[i.val]<475 := by decide

theorem target (same : Bool) : load32 (scan same).memory ((scan same).regs 4)=(0x2c5f0#32) := by
  cases same <;> decide

theorem active (same : Bool) : load32 (scan same).memory 0x2c024=0 := by cases same <;> decide

theorem geometries (same : Bool) (i : Fin cell.ids.length) :
    Geometry (OriginalLineDispatch.view (atIndex (scan same) i.val)) (ray same) (data i.val).line
      (linePointer 0x600200 cell.ids[i.val]) (data i.val).v (data i.val).w := by
  apply callback_geometry (scan same) 1 (by rfl) i.val
  · exact (items same).pointers i (Fixed.ofInt 0)
  · cases same <;> decide
  · have choices : i=0 ∨ i=1 := by
      apply (or_congr Fin.ext_iff Fin.ext_iff).mpr
      change i.val=0 ∨ i.val=1
      have hi : i.val<2 := i.isLt
      omega
    rcases choices with rfl|rfl <;> cases same <;> constructor <;> decide
  · intro a ha
    apply (word_protected a ?_).side
    apply List.mem_append_left
    apply members same a
    exact read_member 1 0x800900 2 (cs same) i.val i.isLt a
      (by
        change a∈OriginalLineSecondPoint.reads (linePointer 0x600200 cell.ids[i.val]!) (data i.val).v (data i.val).w ++ _
        apply List.mem_append_left
        simpa only [getElem!_pos cell.ids i.val i.isLt] using ha)


theorem computed (same : Bool) : ∀ i : Fin cell.ids.length,
    OriginalLineSecondPoint.firstSide (ray same) (data i.val).line≠OriginalLineSecondPoint.lastSide (ray same) (data i.val).line →
    Collision.interceptVector (ray same) ⟨(data i.val).line.x,(data i.val).line.y,(data i.val).line.dx,(data i.val).line.dy⟩=.ok (data i.val).frac := by
  cases same
  · intro _ _; change Collision.interceptVector (ray false) ⟨wall.x,wall.y,wall.dx,wall.dy⟩=.ok (⟨43690⟩ : Fixed); rfl
  · intro i ne; exact False.elim (ne (by dsimp only [data]; decide))

theorem back (same : Bool) : ∀ i : Fin cell.ids.length,
    load32 (scan same).memory (linePointer 0x600200 cell.ids[i.val]+50)=0 ↔ (data i.val).line.back.isNone=true := by
  intro i
  have choices : i=0 ∨ i=1 := by
      apply (or_congr Fin.ext_iff Fin.ext_iff).mpr
      change i.val=0 ∨ i.val=1
      have hi : i.val<2 := i.isLt
      omega
  rcases choices with rfl|rfl <;> cases same <;> decide

def checked (same : Bool) := E1M1ScanContracts.initial (scan same) 1 0x800900 0x600200 (ray same) cell data
  rfl rfl (items same) ids (target same) (active same) (geometries same) (computed same) (back same) (layout same)
def result (same : Bool) := OriginalLineMixedInvariant.finished (scan same) 2 0x2ba20 (E1M1PathMap.resolve 0x600200)
  (checked same) none {trace:=ray same}

theorem collected (same : Bool) : OriginalLineCollection.Tracks (scan same) 0x2ba20 (E1M1PathMap.resolve 0x600200) #[] 2 := by
  constructor
  · intro i hi; simp at hi
  · cases same <;> decide
  · decide

theorem execution (same : Bool) :
    (∃ steps≤569, X86Routine.Prefix OriginalLineMixedInvariant.program [] steps
      ⟨scan same,none,0x2c57f⟩ (result same).1) ∧
    OriginalLineCollection.Tracks (result same).1.core 0x2ba20 (E1M1PathMap.resolve 0x600200) (result same).2.collected 0 := by
  have run := E1M1ScanContracts.through_sentinel (scan same) 1 0x800900 0x600200 (ray same) cell data
    rfl rfl (items same) ids (target same) (active same) (geometries same) (computed same) (back same) (layout same)
    none {trace:=ray same} (collected same)
  exact ⟨run.1,run.2.2.1⟩

example : (result false).2.collected.map (fun hit => (hit.frac.raw.toInt,hit.isLine,hit.id))=#[((43690:Int),true,0)] := by decide +kernel
example : (result true).2.collected=#[] := by decide
#print axioms checked
#print axioms execution
end ScanContractsFixture

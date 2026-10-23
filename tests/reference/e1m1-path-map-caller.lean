import Doom.Proofs.E1M1PathMapCaller
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapCaller
namespace PathMapCallerFixture
-- An unaligned raw lump crosses address zero. Its cell keeps repeated line zero.
def base : Word := 0xfffffffb
def lines : Word := 0x700001
def words : Array Nat := #[0,0,36,23,5,0,0,474,65535]
def cell : Cell := ⟨5,[0,0,474]⟩
def memory : Memory :=
  [(base,0),(base+4,23*65536+36),(base+8,5),(base+12,474*65536),(base+16,65535),
   (0x2c100,base+8),(0x2c10c,base),(0x2c120,lines),
   (0x2c0fc,36),(0x2c110,23),(0x600047,1),(0x2c028,0x71000d),(0x710001,0x20000),(0x710005,1),(0x710009,lines+62)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def state : X86Memory.State :=
  ⟨fun r => if r=0 then 17 else if r=2 then 23 else if r=3 then 0xdeadbeef else if r=4 then 0x600007 else 0,memory⟩

theorem image : WordImage state.memory base words := by
  intro i value h
  have bound : i<9 := by
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp h
    exact hi
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with h0|h0|h0|h0|h0|h0|h0|h0|h0
  all_goals
    subst i
    simp [words] at h
    subst value
    decide +kernel

theorem dims : Dimensions state 36 23 := by
  constructor <;> try decide +kernel
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  all_goals unfold Safe Apart; decide +kernel

theorem globals : Globals state base lines := by
  constructor <;> try decide +kernel
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  all_goals unfold Safe Apart; decide +kernel

theorem image_safe : ImageSafe state base words := by
  have finite : ∀ i : Fin 9, Safe state (base+BitVec.ofNat 32 (2*i.val)) := by
    unfold Safe Apart
    decide +kernel
  intro i hi
  exact finite ⟨i,hi⟩

theorem valid : cell.Valid words := by decide +kernel

theorem joined :
    (∃ n≤30, X86Routine.Prefix program [] n ⟨state,none,0x2ca7f⟩ (scan state)) ∧
    ScanWords (scan state).core lines cell ∧ (scan state).pc=0x2c57f ∧
    (scan state).core.regs 4=state.regs 4-(12#32) :=
  inside_to_scan state none base lines words cell 0 0 36 23 (by decide) dims (by decide) (by decide)
    globals (by decide) valid image image_safe (by decide)

-- The incoming EAX/EDX/EBX are deliberately wrong; the caller must replace them.
example : (call state).core.regs 0=0 ∧ (call state).core.regs 2=0 ∧
    (call state).core.regs 3=(0x2c5f0#32) := by decide +kernel
example : load32 (scan state).core.memory 0x600003=(0x2ca94#32) := by decide +kernel
example : load32 (scan state).core.memory 0x5ffffb=(0x2c5f0#32) := by decide +kernel
example : (scan state).core.regs 2=(5#32) := by decide +kernel
example : OriginalLineCell.itemWord (OriginalLineInvariant.atIndex (scan state).core 1)=0 := by decide +kernel
def hit : Collision.Intercept := ⟨⟨0x20000⟩,true,1⟩
theorem collection : OriginalLineCollection.Tracks state 0x710001 (resolve lines) #[hit] 13 := by
  refine ⟨?_,by decide,by decide⟩
  intro i hi
  have eq : i=0 := by simpa using hi
  subst i
  change OriginalLineFinish.RecordAt state.memory 0x710001 hit (resolve lines hit)
  unfold OriginalLineFinish.RecordAt
  decide +kernel

example : OriginalLineCollection.Tracks (scan state).core 0x710001 (resolve lines) #[hit] 13 := by
  apply collection_preserved state 0x710001 (resolve lines) #[hit] 13 collection
  · unfold Safe Apart; decide +kernel
  · intro i hi off ho
    have eq : i=0 := by simpa using hi
    subst i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl
    all_goals unfold Safe Apart; decide +kernel

-- All outside directions restore caller SP and reach the thing gate. The
-- wrapping stack overlaps the raw lump, so no map-image premise is available.
def outsideState (x y : Int32) : X86Memory.State :=
  ⟨fun r => if r=6 then x.toBitVec else if r=1 then y.toBitVec else if r=4 then 1 else state.regs r,
   store32 memory 65 1⟩
theorem outside_dims (x y : Int32) : Dimensions (outsideState x y) 36 23 := by
  constructor
  · change load32 (store32 memory 65 1) 0x2c0fc=(36#32); decide +kernel
  · change load32 (store32 memory 65 1) 0x2c110=(23#32); decide +kernel
  · decide +kernel
  · decide +kernel
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    all_goals change Apart _ ((1#32)-4) ∧ Apart _ ((1#32)-8) ∧ Apart _ ((1#32)-12)
    all_goals unfold Apart; decide +kernel

theorem outside_joined (x y : Int32) (outside : Collision.pathCellInside x y 36 23=false) :
    (∃ n≤24, X86Routine.Prefix program [] n ⟨outsideState x y,none,0x2ca7f⟩ (resumed (outsideState x y))) ∧
    (resumed (outsideState x y)).pc=0x2ca9c ∧ (resumed (outsideState x y)).core.regs 4=1 ∧
    (resumed (outsideState x y)).core.regs 0=1 := by
  apply outside_to_things _ none x y 36 23 _ (outside_dims x y) rfl rfl outside
  change ((store32 memory 65 1) 65 &&& (1#8) != 0)=true
  decide +kernel

example : (resumed (outsideState (-1) 0)).pc=0x2ca9c := (outside_joined _ _ (by decide)).2.1
example : (resumed (outsideState 0 (-1))).pc=0x2ca9c := (outside_joined _ _ (by decide)).2.1
example : (resumed (outsideState 36 0)).core.regs 4=1 := (outside_joined _ _ (by decide)).2.2.1
example : (resumed (outsideState 0 23)).core.regs 0=1 := (outside_joined _ _ (by decide)).2.2.2

#print axioms joined
#print axioms outside_joined
end PathMapCallerFixture

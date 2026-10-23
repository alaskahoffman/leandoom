import Doom.Proofs.E1M1PathMapBounds
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapBounds
namespace PathMapBoundsFixture
-- An unaligned raw lump crosses address zero. Its cell keeps repeated line zero.
def base : Word := 0xfffffffb
def lines : Word := 0x700001
def words : Array Nat := #[0,0,36,23,5,0,0,474,65535]
def cell : Cell := ⟨5,[0,0,474]⟩
def memory : Memory :=
  [(base,0),(base+4,23*65536+36),(base+8,5),(base+12,474*65536),(base+16,65535),
   (0x2c100,base+8),(0x2c10c,base),(0x2c120,lines),
   (0x2c0fc,36),(0x2c110,23),(0x600003,0x2ca9a),(0x2c028,0x71000d),(0x710001,0x20000),(0x710005,1),(0x710009,lines+62)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def state : X86Memory.State :=
  ⟨fun r => if r=3 then 0x2c5f0 else if r=4 then 0x600003 else 0,memory⟩

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

theorem bounds : OriginalLineBounds.Inputs state 0 0 36 23 := by
  constructor <;> try decide +kernel
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  all_goals unfold Apart; decide +kernel

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
    (∃ n≤24, X86Routine.Prefix program [] n ⟨state,none,0x2c520⟩ (scanStart state)) ∧
    ScanWords (scanStart state).core lines cell ∧ (scanStart state).pc=0x2c57f ∧
    (scanStart state).core.regs 4=state.regs 4-(8#32) :=
  inside_to_scan state none base lines words cell 0 0 36 23 bounds globals (by decide)
    valid image image_safe (by decide)

example : load32 (scanStart state).core.memory 0x5ffffb=(0x2c5f0#32) := by decide +kernel
example : (scanStart state).core.regs 2=(5#32) := by decide +kernel
example : OriginalLineCell.itemWord (OriginalLineInvariant.atIndex (scanStart state).core 1)=0 := by decide +kernel

def hit : Collision.Intercept := ⟨⟨0x20000⟩,true,1⟩
theorem collection : OriginalLineCollection.Tracks state 0x710001 (resolve lines) #[hit] 13 := by
  refine ⟨?_,by decide,by decide⟩
  intro i hi
  have eq : i=0 := by simpa using hi
  subst i
  change OriginalLineFinish.RecordAt state.memory 0x710001 hit (resolve lines hit)
  unfold OriginalLineFinish.RecordAt
  decide +kernel

example : OriginalLineCollection.Tracks (scanStart state).core 0x710001 (resolve lines) #[hit] 13 := by
  apply collection_preserved state 0x710001 (resolve lines) #[hit] 13 collection
  · unfold Safe Apart; decide +kernel
  · intro i hi off ho
    have eq : i=0 := by simpa using hi
    subst i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl
    all_goals unfold Safe Apart; decide +kernel

-- Outside coordinates need no map image. Here the wrapping stack deliberately
-- overlaps the raw lump, demonstrating why the inside-case separation matters.
def outsideState (x y : Int32) : X86Memory.State :=
  ⟨fun r => if r=0 then x.toBitVec else if r=2 then y.toBitVec else if r=4 then 1 else state.regs r,
   store32 memory 1 0x2ca9a⟩
theorem outside_bounds (x y : Int32) : OriginalLineBounds.Inputs (outsideState x y) x y 36 23 := by
  constructor
  · rfl
  · rfl
  · change load32 (store32 memory 1 0x2ca9a) 0x2c0fc=(36#32)
    decide +kernel
  · change load32 (store32 memory 1 0x2ca9a) 0x2c110=(23#32)
    decide +kernel
  · decide +kernel
  · decide +kernel
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    all_goals change Apart _ ((1#32)-4) ∧ Apart _ ((1#32)-8); unfold Apart; decide +kernel

example : (OriginalLineBounds.result (outsideState (-1) 0)).pc=0x2ca9a :=
  (outside_returns _ none (-1) 0 36 23 (outside_bounds _ _) (by decide)).2.2.2
example : (OriginalLineBounds.result (outsideState 0 (-1))).pc=0x2ca9a :=
  (outside_returns _ none 0 (-1) 36 23 (outside_bounds _ _) (by decide)).2.2.2
example : (OriginalLineBounds.result (outsideState 36 0)).core.regs 0=1 :=
  (outside_returns _ none 36 0 36 23 (outside_bounds _ _) (by decide)).2.1
example : (OriginalLineBounds.result (outsideState 0 23)).core.regs 4=(5#32) :=
  (outside_returns _ none 0 23 36 23 (outside_bounds _ _) (by decide)).2.2.1

#print axioms joined
end PathMapBoundsFixture

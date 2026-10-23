import Doom.Proofs.E1M1PathMapSetup
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapSetup
namespace PathMapSetupFixture
-- Diagnostic boundary states, not a claim of reachability from level startup.
def base : Word := 0xfffffffb
def lines : Word := 0x700001
def words : Array Nat := #[0,0,36,23,5,0,0,474,65535]
def cell : Cell := ⟨5,[0,0,474]⟩
def memory : Memory :=
  [(base,0),(base+4,23*65536+36),(base+8,5),(base+12,474*65536),(base+16,65535),
   (0x2c100,base+8),(0x2c10c,base),(0x2c120,lines),(0x2c0fc,36),(0x2c110,23),
   (0x600047,3),(0x2c028,0xdead00),(0x13580,0xffffffff)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def state (ex ey : Fixed) : X86Memory.State :=
  ⟨fun r => if r=0 then (Fixed.ofInt 64).raw.toBitVec else if r=2 then (Fixed.ofInt 64).raw.toBitVec
    else if r=3 then ex.raw.toBitVec else if r=1 then ey.raw.toBitVec
    else if r=4 then 0x600043 else 0,memory⟩

theorem geometry (ex ey : Fixed) :
    OriginalPathInit.Inputs (state ex ey) (Fixed.ofInt 0) (Fixed.ofInt 0) (Fixed.ofInt 64) (Fixed.ofInt 64) ex ey := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · change load32 memory 0x2c104=0; decide +kernel
  · change load32 memory 0x2c108=0; decide +kernel
  · simp [OriginalPathInit.reads,OriginalPathInit.writes,state]
    repeat' constructor
    all_goals unfold Apart; decide +kernel
  · change OriginalPathInit.Separated (state (Fixed.ofInt 0) (Fixed.ofInt 0))
    unfold OriginalPathInit.Separated Apart
    decide +kernel

-- Reduce finite write footprints before invoking kernel computation.
theorem safe_globals (ex ey : Fixed) :
    ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe (state ex ey) a := by
  change ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe (state (Fixed.ofInt 0) (Fixed.ofInt 0)) a
  unfold Safe StackSafe offsets
  change ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120],
    (∀ b∈[(0x60003f#32),0x60003b,0x600037,0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c,
          0x600013,0x600017,0x60001b,0x60000f,0x60001f], Apart a b) ∧
    (∀ off∈[(0#32),32,-4,-8,-12,-16,4,40,44,28,36], Apart a ((0x600007#32)+off))
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_eq,forall_and]
  repeat' constructor
  all_goals unfold Apart; decide +kernel

theorem safe_image (ex ey : Fixed) : ∀ i<words.size, Safe (state ex ey) (base+BitVec.ofNat 32 (2*i)) := by
  have finite : ∀ i : Fin 9, Safe (state (Fixed.ofInt 0) (Fixed.ofInt 0)) (base+BitVec.ofNat 32 (2*i.val)) := by
    unfold Safe StackSafe offsets
    change ∀ i : Fin 9,
      (∀ b∈[(0x60003f#32),0x60003b,0x600037,0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c,
          0x600013,0x600017,0x60001b,0x60000f,0x60001f], Apart (base+BitVec.ofNat 32 (2*i.val)) b) ∧
      (∀ off∈[(0#32),32,-4,-8,-12,-16,4,40,44,28,36], Apart (base+BitVec.ofNat 32 (2*i.val)) ((0x600007#32)+off))
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_eq,forall_and]
    repeat' constructor
    all_goals unfold Apart; decide +kernel
  intro i hi
  exact finite ⟨i,hi⟩

theorem image : WordImage memory base words := by
  intro i value h
  have bound : i<9 := (Array.getElem?_eq_some_iff.mp h).1
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with h0|h0|h0|h0|h0|h0|h0|h0|h0
  all_goals subst i; simp [words] at h; subst value; decide +kernel

theorem map_inputs (ex ey : Fixed) : MapInputs (state ex ey) base lines words 36 23 := by
  refine ⟨?_,?_,by decide,by decide,?_,?_,?_,safe_globals ex ey,image,safe_image ex ey⟩
  all_goals change load32 memory _=_; decide +kernel

theorem retained (ex ey : Fixed) :
    E1M1PathMapCaller.Dimensions (grid (state ex ey)).core 36 23 ∧
    E1M1PathMapCaller.Globals (grid (state ex ey)).core base lines ∧
    WordImage (grid (state ex ey)).core.memory base words ∧
    E1M1PathMapCaller.ImageSafe (grid (state ex ey)).core base words :=
  map_at_grid _ (Fixed.ofInt 0) (Fixed.ofInt 0) (Fixed.ofInt 64) (Fixed.ofInt 64) ex ey (geometry ex ey) base lines words 36 23 (map_inputs ex ey)

theorem cursor_safe (ex ey : Fixed) : StackSafe ((state ex ey).regs 4-(60#32)) (0x2c028#32) := by
  simp [StackSafe,offsets,state]
  unfold Apart
  decide +kernel

theorem collection (ex ey : Fixed) :
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (grid (state ex ey)).core).core
      0x2ba20 (resolve lines) #[] cell.ids.length :=
  initial_collection_at_scan _ (Fixed.ofInt 0) (Fixed.ofInt 0) (Fixed.ofInt 64) (Fixed.ofInt 64) ex ey (geometry ex ey)
    words cell (by decide) (resolve lines) (cursor_safe ex ey)

-- All nine combinations of negative, stationary and positive grid directions.
def endpoint (i : Nat) := Fixed.ofInt (if i=0 then -64 else if i=1 then 64 else 192)
def direction (i : Nat) : Word := if i=0 then -1 else if i=1 then 0 else 1
example : ∀ k : Fin 9,
    (grid (state (endpoint (k.val%3)) (endpoint (k.val/3)))).core.regs 4=(0x600007#32) ∧
    (grid (state (endpoint (k.val%3)) (endpoint (k.val/3)))).core.regs 6=0 ∧
    (grid (state (endpoint (k.val%3)) (endpoint (k.val/3)))).core.regs 1=0 ∧
    load32 (grid (state (endpoint (k.val%3)) (endpoint (k.val/3)))).core.memory 0x600027=direction (k.val%3) ∧
    load32 (grid (state (endpoint (k.val%3)) (endpoint (k.val/3)))).core.memory 0x600023=direction (k.val/3) := by decide +kernel
example : load32 (E1M1PathMapCaller.scan (grid (state (Fixed.ofInt 192) (Fixed.ofInt (-64)))).core).core.memory
    0x2c028=(0x2ba20#32) := (collection _ _).cursor
example : load32 memory 0x2c028≠(0x2ba20#32) := by decide +kernel

example : load32 (grid (state (Fixed.ofInt 192) (Fixed.ofInt (-64)))).core.memory 0x13580=0 := by decide +kernel

#print axioms retained
#print axioms collection
end PathMapSetupFixture

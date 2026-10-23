import Doom.Proofs.E1M1PathMapQuery
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapQuery
namespace PathMapQueryFixture
-- Diagnostic query-entry memory, not asserted reachable from level startup.
def base : Word := 0xfffffffb
def lines : Word := 0x700001
def words : Array Nat := #[0,0,36,23,5,0,0,474,65535]
def memory : Memory :=
  [(base,0),(base+4,23*65536+36),(base+8,5),(base+12,474*65536),(base+16,65535),
   (0x2c100,base+8),(0x2c10c,base),(0x2c120,lines),(0x2c0fc,36),(0x2c110,23),
   (0x2c104,0xffff0000),(0x2c108,0x10000),
   (0x70010d,64*65536),(0x700111,64*65536),(0x700115,0),(0x700145,56*65536),
   (0x13584,0x800001),(0x800001,65536),(0x5a84,0),
   (0x2b9f8,0x12345678),(0x2c028,0xdead00),(0x13580,0xffffffff)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def state : X86Memory.State :=
  ⟨fun r => if r=0 then 0x700101 else if r=2 then 0 else if r=3 then 1024*65536
    else if r=4 then 0x60005f else 0x11223344,memory⟩

-- An explicit union of the queried write footprints, all relative to entry SP.
def destinations : List Word :=
  [0x60005b,0x600057,0x600053,0x60004f,
   0x60004b,0x2b9ac,0x2b9b8,0x600047,0x2b9f8,0x2b9a8,0x2c1e4,0x2c1e8,0x600043,
   0x60003f,0x60003b,0x600037,0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c,
   0x600013,0x600017,0x60001b,0x60000f,0x60001f,
   0x600007,0x600027,0x600003,0x5fffff,0x5ffffb,0x5ffff7,0x60000b,0x60002f,0x600033,0x600023,0x60002b]

theorem safe_of_destinations (a : Word) (h : ∀ b∈destinations, Apart a b) : Safe state a := by
  constructor
  · intro b hb
    apply h
    simp [OriginalAimQuery.saveWrites,state] at hb
    rcases hb with rfl|rfl|rfl|rfl <;> simp [destinations]
  · intro b hb
    apply h
    simp [OriginalAimSetup.writes,withStack,state,write] at hb
    simp [destinations]
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · constructor
    · intro b hb
      apply h
      simp [OriginalPathInit.writes,withStack,state,write] at hb
      simp [destinations]
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    · intro off ho
      have finite : ∀ off∈E1M1PathMapSetup.offsets, (0x600007#32)+off∈destinations := by
        simp [E1M1PathMapSetup.offsets,destinations]
      exact h _ (finite off ho)

theorem safe_globals :
    ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120,0x2c104,0x2c108], Safe state a := by
  intro a ha
  apply safe_of_destinations
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [destinations]
  all_goals repeat' constructor
  all_goals unfold Apart; decide +kernel

theorem safe_image : ∀ i<words.size, Safe state (base+BitVec.ofNat 32 (2*i)) := by
  have finite : ∀ i : Fin 9, ∀ b∈destinations, Apart (base+BitVec.ofNat 32 (2*i.val)) b := by
    simp only [destinations,List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_eq,forall_and]
    repeat' constructor
    all_goals unfold Apart; decide +kernel
  intro i hi
  exact safe_of_destinations _ (finite ⟨i,hi⟩)

theorem image : WordImage memory base words := by
  intro i value h
  have bound : i<9 := (Array.getElem?_eq_some_iff.mp h).1
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with h0|h0|h0|h0|h0|h0|h0|h0|h0
  all_goals subst i; simp [words] at h; subst value; decide +kernel

theorem map_inputs : MapInputs state base lines words 36 23 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,?_,image,safe_image⟩
  intro a ha
  apply safe_globals
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp

theorem joined :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimSetup.program [] 36 ⟨state,none,0x2bb80⟩ (traversal state) ∧
    E1M1PathMapSetup.MapInputs (traversal state).core base lines words 36 23 :=
  query_execution state none base lines words 36 23 map_inputs

-- Original setup writes occur; the map proof does not pretend all memory stays equal.
example : (traversal state).core.regs 4=(0x600043#32) := by decide +kernel
example : load32 (traversal state).core.memory 0x60004b=(0x2b760#32) := by decide +kernel
example : load32 (traversal state).core.memory 0x600047=(3#32) := by decide +kernel
example : load32 (traversal state).core.memory 0x600043=(0x2bbff#32) := by decide +kernel
example : load32 (traversal state).core.memory 0x2b9f8=0 := by decide +kernel
example : load32 memory 0x2b9f8≠0 := by decide +kernel
example : (traversal state).core.regs 0=(64*65536#32) ∧
    (traversal state).core.regs 3=(1088*65536#32) := by decide +kernel

theorem origins : load32 (traversal state).core.memory 0x2c104=(0xffff0000#32) ∧
    load32 (traversal state).core.memory 0x2c108=(0x10000#32) := by
  simpa only [show (Fixed.ofInt (-1)).raw.toBitVec=(0xffff0000#32) by decide,
    show (Fixed.ofInt 1).raw.toBitVec=(0x10000#32) by decide] using
   origins_at_traversal state (Fixed.ofInt (-1)) (Fixed.ofInt 1) (by decide) (by decide)
    (safe_globals _ (by simp)) (safe_globals _ (by simp))

example : E1M1PathMapSetup.StackSafe ((traversal state).core.regs 4-(60#32)) (0x2c028#32) := by
  apply cursor_at_traversal
  unfold E1M1PathMapSetup.StackSafe E1M1PathMapSetup.offsets
  simp
  unfold Apart
  decide +kernel

#print axioms joined
#print axioms origins
end PathMapQueryFixture

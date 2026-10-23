import Doom.Proofs.E1M1AimGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimGeometry
open E1M1PathMapQuery (traversal)
namespace AimGeometryFixture
-- Diagnostic query-entry states; not a startup reachability theorem.
def angleOf (i : Fin 4) : Angle := ⟨UInt32.ofNat (if i=0 then 0 else if i=1 then 0x40000000 else if i=2 then 0x80000000 else 0xffffffff)⟩
def thing : Collision.SolidThing :=
  {x := Fixed.ofInt 64,y := Fixed.ofInt 64,z := Fixed.ofInt (-8),radius := Fixed.ofInt 20}
def memory (angle : Angle) : Memory :=
  [(0x2c104#32,0xffff0000#32),(0x2c108,0x10000),
   (0x70010d,thing.x.raw.toBitVec),(0x700111,thing.y.raw.toBitVec),
   (0x700115,thing.z.raw.toBitVec),(0x700145,thing.height.raw.toBitVec),
   (0x13584,0x7a84),((angle.raw.toBitVec >>> 19 <<< 2)+0x7a84,angle.fineCosine.raw.toBitVec),
   ((angle.raw.toBitVec >>> 19 <<< 2)+0x5a84,angle.fineSine.raw.toBitVec),
   (0x2b9f8,0x12345678),(0x2c028,0xdead00),(0x13580,0xffffffff)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def state (angle : Angle) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x700101 else if r=2 then angle.raw.toBitVec else if r=3 then 1024*65536
    else if r=4 then 0x60005f else 0x11223344,memory angle⟩
def destinations : List Word :=
  [0x60005b,0x600057,0x600053,0x60004f,
   0x60004b,0x2b9ac,0x2b9b8,0x600047,0x2b9f8,0x2b9a8,0x2c1e4,0x2c1e8,0x600043,
   0x60003f,0x60003b,0x600037,0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c,
   0x600013,0x600017,0x60001b,0x60000f,0x60001f,
   0x600007,0x600027,0x600003,0x5fffff,0x5ffffb,0x5ffff7,0x60000b,0x60002f,0x600033,0x600023,0x60002b]

theorem safe_of_destinations (angle : Angle) (a : Word) (h : ∀ b∈destinations, Apart a b) : E1M1PathMapQuery.Safe (state angle) a := by
  constructor
  · intro b hb
    apply h
    simp [OriginalAimQuery.saveWrites,state] at hb
    rcases hb with rfl|rfl|rfl|rfl <;> simp [destinations]
  · intro b hb
    apply h
    simp [OriginalAimSetup.writes,E1M1PathMapQuery.withStack,state,write] at hb
    simp [destinations]
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · constructor
    · intro b hb
      apply h
      simp [OriginalPathInit.writes,E1M1PathMapQuery.withStack,state,write] at hb
      simp [destinations]
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    · intro off ho
      have finite : ∀ off∈E1M1PathMapSetup.offsets, (0x600007#32)+off∈destinations := by
        simp [E1M1PathMapSetup.offsets,destinations]
      simpa [E1M1PathMapQuery.withStack,state,write] using h _ (finite off ho)


theorem safe_reads (angle : Angle) :
    ∀ a∈[(0x2c104#32),0x2c108,0x70010d,0x700111,0x700115,0x700145],
      E1M1PathMapQuery.Safe (state angle) a := by
  intro a ha
  apply safe_of_destinations
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [destinations]
  all_goals repeat' constructor
  all_goals unfold Apart; decide +kernel

theorem samples (i : Fin 4) : RaySamples (state (angleOf i)) (angleOf i) (Fixed.ofInt 1024) := by
  refine ⟨by rfl,by rfl,?_,?_,?_,?_⟩
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · intro a ha b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals simp [OriginalAimQuery.saveWrites,state] at hb
    all_goals rcases hb with rfl|rfl|rfl|rfl
    all_goals revert i; unfold Apart; decide +kernel

theorem inputs (i : Fin 4) : Inputs (state (angleOf i)) thing (angleOf i) (Fixed.ofInt 1024)
    (Fixed.ofInt (-1)) (Fixed.ofInt 1) := by
  refine ⟨samples i,?_,?_,?_,?_,?_,?_,?_,safe_reads _ _ (by simp),safe_reads _ _ (by simp),?_,?_,?_⟩
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · intro a ha
    apply safe_reads
    simp [OriginalAimSetup.actorReads,state] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> simp
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl|rfl|rfl|rfl
    all_goals simp only [state,memory,List.foldl_cons,List.foldl_nil]
    all_goals repeat first
      | rw [load_store]
      | rw [load_store_apart _ _ _ _ (by unfold Apart; decide +kernel)]
    all_goals rfl
  · unfold OriginalAimSetup.Separated Apart
    revert i
    decide +kernel
  · simp [OriginalPathInit.writes,E1M1PathMapQuery.withStack,state,write]
    repeat' constructor
    all_goals unfold Apart; decide +kernel
  · unfold OriginalPathInit.Separated Apart
    revert i
    decide +kernel

theorem joined (i : Fin 4) :
    ∃ n, n≤96 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PathInit.program [] n
      ⟨state (angleOf i),none,0x2bb80⟩ (OriginalPathInit.result (traversal (state (angleOf i))).core) ∧
    OriginalPathInit.Ready (traversal (state (angleOf i))).core
      (OriginalPathInit.result (traversal (state (angleOf i))).core)
      (Collision.pathStart (Fixed.ofInt (-1)) (Fixed.ofInt 1) thing.x thing.y
        (thing.attackEndpoint (angleOf i) (Fixed.ofInt 1024)).1
        (thing.attackEndpoint (angleOf i) (Fixed.ofInt 1024)).2) :=
  query_path_correspondence _ _ _ _ _ _ _ (inputs i)

example (i : Fin 4) : load32 (traversal (state (angleOf i))).core.memory 0x2b9a8=(28*65536#32) := by
  have h := OriginalAimSetup.live_height _ _ _ _ (setup_inputs _ _ _ _ _ _ (inputs i))
  exact h
example (i : Fin 4) : load32 (traversal (state (angleOf i))).core.memory 0x2b9f8=0 := by
  exact OriginalAimSetup.stored_target _ (setup_inputs _ _ _ _ _ _ (inputs i)).separated
#print axioms joined
end AimGeometryFixture

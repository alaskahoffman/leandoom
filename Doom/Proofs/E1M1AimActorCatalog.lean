import Doom.Proofs.E1M1AimActorCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1MinimumScan (address)
open E1M1HistoryDispatch (Selection)
open E1M1AimMapFrame (StableWord)
open E1M1AimHistoryCycle (Frame)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimCatalog (Portal)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Only actor fields read by aiming, with protection from every possible
continuing callback, fraction mark, cursor store and next CALL. -/
structure Entry (s : X86Memory.State) (pointer : Word) (actor : SolidThing) : Prop where
  flagsSafe : StableWord s (pointer+104)
  zSafe : StableWord s (pointer+20)
  heightSafe : StableWord s (pointer+68)
  flags : (s.memory (pointer+104) &&& (4#8) != 0)=actor.shootable
  z : load32 s.memory (pointer+20)=actor.z.raw.toBitVec
  height : load32 s.memory (pointer+68)=actor.height.raw.toBitVec

/-- Catalog entries are indexed by the immutable original collection. This
covers every actor hit and does not classify line hits as actors. -/
structure Catalog (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (initial : Array Intercept) (resolve : Intercept → Word) (who : Word) : Prop where
  shooterSafe : StableWord s 0x2b9ac
  shooterWord : load32 s.memory 0x2b9ac=who
  saveSafe : E1M1AimActorReturn.Safe s
  actors : ∀ i<initial.size, initial[i]!.isLine=false →
    initial[i]!.id<scene.things.size ∧ (resolve initial[i]! = who ↔ initial[i]!.id=shooter) ∧
    Entry s (resolve initial[i]!) scene.things[initial[i]!.id]!

/-- All entries survive, including actors other than the just-processed hit. -/
theorem entry_preserved (s : X86Memory.State) (out : X86Control.State) (marked : Nat)
    (pointer : Word) (actor : SolidThing) (frame : Frame s out)
    (stack : out.core.regs 4=s.regs 4) (selected : s.regs 3=address marked) (bounded : marked<128)
    (entry : Entry s pointer actor) : Entry out.core pointer actor := by
  refine ⟨E1M1AimMapFrame.stable_word s out.core _ stack entry.flagsSafe,
    E1M1AimMapFrame.stable_word s out.core _ stack entry.zSafe,
    E1M1AimMapFrame.stable_word s out.core _ stack entry.heightSafe,?_,?_,?_⟩
  · rw [E1M1AimMapFrame.byte s out marked _ frame selected bounded entry.flagsSafe]; exact entry.flags
  · exact (E1M1AimMapFrame.word s out marked _ frame selected bounded entry.zSafe).trans entry.z
  · exact (E1M1AimMapFrame.word s out marked _ frame selected bounded entry.heightSafe).trans entry.height

theorem preserved (s : X86Memory.State) (out : X86Control.State) (marked : Nat)
    (scene : Scene) (shooter : Nat) (initial : Array Intercept) (resolve : Intercept → Word) (who : Word)
    (frame : Frame s out) (stack : out.core.regs 4=s.regs 4)
    (pointer : s.regs 3=address marked) (bounded : marked<128)
    (catalog : Catalog s scene shooter initial resolve who) : Catalog out.core scene shooter initial resolve who := by
  refine ⟨E1M1AimMapFrame.stable_word s out.core _ stack catalog.shooterSafe,
    (E1M1AimMapFrame.word s out marked _ frame pointer bounded catalog.shooterSafe).trans catalog.shooterWord,
    E1M1AimActorStop.safe_transfer s out.core stack catalog.saveSafe,?_⟩
  intro i inside kind
  obtain ⟨valid,identity,entry⟩ := catalog.actors i inside kind
  exact ⟨valid,identity,entry_preserved s out marked _ _ frame stack pointer bounded entry⟩

/-- The actor's ten stack-write offsets are already included in opening protection. -/
theorem opening_reads (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈E1M1AimOpeningFrame.writes (s.regs 4), Apart a b) :
    E1M1AimActorBottomReject.ReadSafe s a := by
  intro off h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact safe _ (by simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes])

/-- The exact existing actor-cycle premises, derived at a selected actor. -/
structure Inputs (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hit : Intercept) (pointer who : Word) : Prop where
  valid : hit.id<scene.things.size
  shooterSafe : E1M1AimWall.Safe (s.regs 4) 0x2b9ac
  flagsSafe : E1M1AimWall.Safe (s.regs 4) (pointer+104)
  shooterWord : load32 s.memory 0x2b9ac=who
  identity : pointer=who ↔ hit.id=shooter
  flags : (s.memory (pointer+104) &&& (4#8) != 0)=scene.things[hit.id]!.shootable
  topSafe : E1M1AimActorTopEntry.ReadSafe s pointer
  bottomSafe : E1M1AimActorBottomEntry.ReadSafe s pointer
  z : load32 s.memory (pointer+20)=scene.things[hit.id]!.z.raw.toBitVec
  height : load32 s.memory (pointer+68)=scene.things[hit.id]!.height.raw.toBitVec
  saveSafe : E1M1AimActorReturn.Safe s

/-- No actor image, pointer identity or new read-separation premise is requested
at the reached callback: the catalog and persistent traversal layout supply them. -/
theorem inputs (s : X86Control.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance : Fixed)
    (target sp who : Word) (fraction : Int32) (j : Nat)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp s fraction j)
    (before : Persistent s.core initial work resolve portals distance thing.shootHeight)
    (catalog : Catalog s.core scene shooter initial resolve who) (isThing : (work[j]!).isLine=false) :
    Inputs s.core scene shooter work[j]! (resolve initial[j]!) who := by
  have kind : initial[j]!.isLine=false := by rw [← selection.original]; exact isThing
  obtain ⟨valid,identity,entry⟩ := catalog.actors j selection.inside kind
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have fractionSafe : E1M1AimActorBottomReject.ReadSafe s.core (s.core.regs 0) := by
    rw [selection.argument]
    simpa only [BitVec.add_zero] using E1M1AimActorBottomCycle.read_safe s.core _
      (before.layout.recordsSafe j inside (0#32) (by simp))
  have low := opening_reads s.core (0x2c1e4#32) (before.layout.floorReads _ (by simp))
  have high := opening_reads s.core (0x2c1e8#32) (before.layout.ceilingReads _ (by simp))
  have range := E1M1AimActorBottomCycle.read_safe s.core _ (before.query (0x2b9b8#32) (by simp)).1
  have eye := E1M1AimActorBottomCycle.read_safe s.core _ (before.query (0x2b9a8#32) (by simp)).1
  have z := E1M1AimActorBottomCycle.read_safe s.core _ entry.zSafe.1
  have ht := E1M1AimActorBottomCycle.read_safe s.core _ entry.heightSafe.1
  refine ⟨by simpa only [selection.original] using valid,catalog.shooterSafe.1.1,entry.flagsSafe.1.1,
    catalog.shooterWord,by simpa only [selection.original] using identity,
    by simpa only [selection.original] using entry.flags,?_,?_,
    by simpa only [selection.original] using entry.z,by simpa only [selection.original] using entry.height,catalog.saveSafe⟩
  · intro a member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    · exact fractionSafe
    · exact range
    · exact z
    · exact ht
    · exact eye
    · exact low
  · intro a member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact z
    · exact eye
    · exact low
    · exact high
end Doom.Proofs.E1M1AimActorCatalog

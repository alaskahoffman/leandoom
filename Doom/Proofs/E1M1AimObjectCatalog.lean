import Doom.Proofs.E1M1AimHelperEntry
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimObjectCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (Storage)
open E1M1AimCatalog (Portal)

/-- Memory contents only. Region placement supplies the three persistent guards. -/
structure ActorValues (memory : Memory) (pointer : Word) (actor : SolidThing) : Prop where
  flags : (memory (pointer+104) &&& (4#8) != 0)=actor.shootable
  z : load32 memory (pointer+20)=actor.z.raw.toBitVec
  height : load32 memory (pointer+68)=actor.height.raw.toBitVec

/-- Preserve classification and exact DOS pointer/height/flag contents. -/
def PortalValues (memory : Memory) (hit : Intercept) (line : Word) (p : Portal) : Prop :=
  hit.isLine=true ∧ E1M1AimOpeningFrame.Image memory line p.front p.back p.ff p.fc p.bf p.bc ∧
  memory (line+16) &&& (4#8)≠0

def WallValues (memory : Memory) (hit : Intercept) (line : Word) : Prop :=
  hit.isLine=true ∧ memory (line+16) &&& (4#8)=0

theorem actor (stack : Region) (sp : Word) (s : X86Memory.State) (pointer : Word) (thing : SolidThing)
    (storage : Storage stack pointer 108) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (position : s.regs 4=sp-140) (values : ActorValues s.memory pointer thing) :
    E1M1AimActorCatalog.Entry s pointer thing := by
  have safe (a : Word) (ha : a∈[pointer+104,pointer+20,pointer+68]) :=
    E1M1AimWalkRegions.ordered stack sp a s reserve
      (E1M1AimObjectRegions.actor stack pointer storage a ha) position
  exact ⟨safe _ (by simp),safe _ (by simp),safe _ (by simp),values.flags,values.z,values.height⟩

theorem portal (stack : Region) (sp : Word) (s : X86Memory.State) (hit : Intercept)
    (line : Word) (p : Portal) (lineStorage : Storage stack line 62)
    (frontStorage : Storage stack p.front 8) (backStorage : Storage stack p.back 8)
    (reserve : E1M1AimWalkRegions.Reserve stack sp) (position : s.regs 4=sp-140)
    (values : PortalValues s.memory hit line p) : E1M1AimCatalog.Entry s hit line p := by
  refine ⟨values.1,?_,values.2⟩
  intro a ha
  exact E1M1AimWalkRegions.ordered stack sp a s reserve
    (E1M1AimObjectRegions.opening stack line p.front p.back lineStorage frontStorage backStorage a ha) position

theorem wall (stack : Region) (sp : Word) (s : X86Memory.State) (hit : Intercept) (line : Word)
    (storage : Storage stack line 62) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (position : s.regs 4=sp-140) (values : WallValues s.memory hit line) :
    hit.isLine=true ∧ E1M1AimMapFrame.StableWord s (line+16) ∧ s.memory (line+16) &&& (4#8)=0 := by
  exact ⟨values.1,E1M1AimWalkRegions.ordered stack sp _ s reserve
    (E1M1AimObjectRegions.wall stack line storage) position,values.2⟩

/-- Classify each original hit before choosing its actor or line storage prefix. -/
theorem actors (stack : Region) (sp : Word) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept) (lookup : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (placement : E1M1AimCatalogRegions.Layout stack hits lookup portals)
    (reserve : E1M1AimWalkRegions.Reserve stack sp) (position : s.regs 4=sp-140)
    (values : ∀ i<hits.size, hits[i]!.isLine=false →
      hits[i]!.id<scene.things.size ∧ (lookup hits[i]! = who ↔ hits[i]!.id=shooter) ∧
      ActorValues s.memory (lookup hits[i]!) scene.things[hits[i]!.id]!) :
    ∀ i<hits.size, hits[i]!.isLine=false →
      hits[i]!.id<scene.things.size ∧ (lookup hits[i]! = who ↔ hits[i]!.id=shooter) ∧
      E1M1AimActorCatalog.Entry s (lookup hits[i]!) scene.things[hits[i]!.id]! := by
  intro i hi kind
  obtain ⟨valid,identity,image⟩ := values i hi kind
  have storage : Storage stack (lookup hits[i]!) 108 := by
    simpa [kind] using placement.hit i hi
  exact ⟨valid,identity,actor stack sp s _ _ storage reserve position image⟩

theorem portals (stack : Region) (sp : Word) (s : X86Memory.State)
    (hits : Array Intercept) (lookup : Intercept → Word) (openings : Nat → Option Portal)
    (placement : E1M1AimCatalogRegions.Layout stack hits lookup openings)
    (reserve : E1M1AimWalkRegions.Reserve stack sp) (position : s.regs 4=sp-140)
    (values : ∀ i<hits.size, ∀ p, openings i=some p → PortalValues s.memory hits[i]! (lookup hits[i]!) p) :
    E1M1AimCatalog.Catalog s hits lookup openings := by
  intro i hi p hp
  have storage := placement.portal i hi p hp
  exact portal stack sp s _ _ p storage.1 storage.2.1 storage.2.2 reserve position (values i hi p hp)

theorem walls (stack : Region) (sp : Word) (s : X86Memory.State)
    (hits : Array Intercept) (lookup : Intercept → Word) (openings : Nat → Option Portal) (solid : Nat → Prop)
    (placement : E1M1AimCatalogRegions.Layout stack hits lookup openings)
    (reserve : E1M1AimWalkRegions.Reserve stack sp) (position : s.regs 4=sp-140)
    (values : ∀ i<hits.size, solid i → WallValues s.memory hits[i]! (lookup hits[i]!)) :
    E1M1AimWallCatalog.Catalog s hits lookup solid := by
  intro i hi hs
  have image := values i hi hs
  have storage : Storage stack (lookup hits[i]!) 62 := by
    simpa [image.1] using placement.hit i hi
  exact wall stack sp s _ _ storage reserve position image

/-- Derive an actor's persistent guard once, then reuse the actual cycle frame.
The frame and reached stack/selected-record relations remain execution premises. -/
theorem actor_preserved (stack : Region) (sp : Word) (s : X86Memory.State)
    (out : X86Control.State) (marked : Nat) (pointer : Word) (thing : SolidThing)
    (storage : Storage stack pointer 108) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (position : s.regs 4=sp-140) (values : ActorValues s.memory pointer thing)
    (frame : E1M1AimHistoryCycle.Frame s out) (sameStack : out.core.regs 4=s.regs 4)
    (selected : s.regs 3=E1M1MinimumScan.address marked) (bounded : marked<128) :
    E1M1AimActorCatalog.Entry out.core pointer thing := by
  exact E1M1AimActorCatalog.entry_preserved s out marked pointer thing frame sameStack selected bounded
    (actor stack sp s pointer thing storage reserve position values)
end Doom.Proofs.E1M1AimObjectCatalog

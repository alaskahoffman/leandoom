import Doom.Proofs.E1M1AimInitialCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimEntryCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimCatalog (Portal)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- A word image with an explicit protected-address predicate. This interface
can consume a query/collection frame without assuming a preceding hit or mark. -/
def Image (before after : Memory) (P : Word → Prop) : Prop :=
  ∀ a, P a → load32 after a=load32 before a

theorem byte (before after : Memory) (P : Word → Prop) (image : Image before after P)
    (a : Word) (safe : P a) : after a=before a := by
  have low := congrArg (fun w : Word => w.extractLsb' 0 8) (image a safe)
  simpa only [E1M1PathCell.low_byte] using low

theorem half (before after : Memory) (P : Word → Prop) (image : Image before after P)
    (a : Word) (safe : P a) : load16 after a=load16 before a := by
  have low := congrArg (fun w : Word => w.extractLsb' 0 16) (image a safe)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using low

def ActorReads (initial : Array Intercept) (resolve : Intercept → Word) (P : Word → Prop) : Prop :=
  P 0x2b9ac ∧ ∀ i<initial.size, initial[i]!.isLine=false →
    ∀ a∈[resolve initial[i]!+104,resolve initial[i]!+20,resolve initial[i]!+68], P a

def WallReads (initial : Array Intercept) (resolve : Intercept → Word)
    (walls : Nat → Prop) (P : Word → Prop) : Prop :=
  ∀ i<initial.size, walls i → P (resolve initial[i]!+16)

def PortalReads (initial : Array Intercept) (resolve : Intercept → Word)
    (portals : Nat → Option Portal) (P : Word → Prop) : Prop :=
  ∀ i<initial.size, ∀ p, portals i=some p →
    ∀ a∈(resolve initial[i]!+16)::E1M1OpeningHeights.reads (resolve initial[i]!) p.front p.back, P a

/-- Source flags and dimensions, and their static future-callback protection,
transfer without a selected-hit or sentinel-store premise. -/
theorem actor_entry (s t : X86Memory.State) (P : Word → Prop)
    (image : Image s.memory t.memory P) (stack : t.regs 4=s.regs 4)
    (pointer : Word) (actor : SolidThing)
    (reads : ∀ a∈[pointer+104,pointer+20,pointer+68], P a)
    (entry : E1M1AimActorCatalog.Entry s pointer actor) :
    E1M1AimActorCatalog.Entry t pointer actor := by
  refine ⟨E1M1AimMapFrame.stable_word s t _ stack entry.flagsSafe,
    E1M1AimMapFrame.stable_word s t _ stack entry.zSafe,
    E1M1AimMapFrame.stable_word s t _ stack entry.heightSafe,?_,?_,?_⟩
  · rw [byte _ _ P image _ (reads _ (by simp))]; exact entry.flags
  · exact (image _ (reads _ (by simp))).trans entry.z
  · exact (image _ (reads _ (by simp))).trans entry.height

theorem actors (s t : X86Memory.State) (scene : Scene) (shooter : Nat)
    (initial : Array Intercept) (resolve : Intercept → Word) (who : Word)
    (P : Word → Prop) (image : Image s.memory t.memory P) (stack : t.regs 4=s.regs 4)
    (reads : ActorReads initial resolve P)
    (catalog : E1M1AimActorCatalog.Catalog s scene shooter initial resolve who) :
    E1M1AimActorCatalog.Catalog t scene shooter initial resolve who := by
  refine ⟨E1M1AimMapFrame.stable_word s t _ stack catalog.shooterSafe,
    (image _ reads.1).trans catalog.shooterWord,
    E1M1AimActorStop.safe_transfer s t stack catalog.saveSafe,?_⟩
  intro i hi kind
  obtain ⟨valid,identity,entry⟩ := catalog.actors i hi kind
  exact ⟨valid,identity,actor_entry s t P image stack _ _ (reads.2 i hi kind) entry⟩

theorem walls (s t : X86Memory.State) (initial : Array Intercept)
    (resolve : Intercept → Word) (solid : Nat → Prop)
    (P : Word → Prop) (image : Image s.memory t.memory P) (stack : t.regs 4=s.regs 4)
    (reads : WallReads initial resolve solid P)
    (catalog : E1M1AimWallCatalog.Catalog s initial resolve solid) :
    E1M1AimWallCatalog.Catalog t initial resolve solid := by
  intro i hi listed
  obtain ⟨kind,safe,flags⟩ := catalog i hi listed
  exact ⟨kind,E1M1AimMapFrame.stable_word s t _ stack safe,
    by rw [byte _ _ P image _ (reads i hi listed)]; exact flags⟩

theorem portal_entry (s t : X86Memory.State) (hit : Intercept) (line : Word) (p : Portal)
    (P : Word → Prop) (image : Image s.memory t.memory P) (stack : t.regs 4=s.regs 4)
    (reads : ∀ a∈(line+16)::E1M1OpeningHeights.reads line p.front p.back, P a)
    (entry : E1M1AimCatalog.Entry s hit line p) : E1M1AimCatalog.Entry t hit line p := by
  obtain ⟨kind,region,fields,two⟩ := entry
  have keep (a : Word) (member : a∈E1M1OpeningHeights.reads line p.front p.back) :=
    image a (reads a (List.mem_cons_of_mem _ member))
  refine ⟨kind,E1M1AimMapFrame.region s t line p.front p.back stack region,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [half _ _ P image _ (reads _ (by simp [E1M1OpeningHeights.reads]))]; exact fields.side
    · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans fields.frontPtr
    · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans fields.backPtr
    · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans fields.frontFloor
    · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans fields.frontCeiling
    · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans fields.backFloor
    · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans fields.backCeiling
  · rw [byte _ _ P image _ (reads _ (by simp))]; exact two

theorem portals (s t : X86Memory.State) (initial : Array Intercept)
    (resolve : Intercept → Word) (catalogue : Nat → Option Portal)
    (P : Word → Prop) (image : Image s.memory t.memory P) (stack : t.regs 4=s.regs 4)
    (reads : PortalReads initial resolve catalogue P)
    (catalog : E1M1AimCatalog.Catalog s initial resolve catalogue) :
    E1M1AimCatalog.Catalog t initial resolve catalogue := by
  intro i hi p listed
  exact portal_entry s t initial[i]! (resolve initial[i]!) p P image stack
    (reads i hi p listed) (catalog i hi p listed)
end Doom.Proofs.E1M1AimEntryCatalog

import Doom.Proofs.E1M1AimObjectEntry
import Doom.Proofs.E1M1LineLoad
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimLoadedPortal
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1AimCatalog (Portal)

/-- Loader input uses side-table targets, not already-cached line pointers. -/
def line (address : Word) (p : Portal) : OriginalGroupOutput.Line := ⟨address,p.front,p.back⟩
def sectorReads (p : Portal) : List Word := [p.front,p.front+4,p.back,p.back+4]
def SectorValues (m : Memory) (p : Portal) : Prop :=
  load32 m p.front=p.ff ∧ load32 m (p.front+4)=p.fc ∧
  load32 m p.back=p.bf ∧ load32 m (p.back+4)=p.bc
/-- Copying side indices and caching pointers must not overwrite sector data. -/
def SectorSafe (address : Word) (p : Portal) : Prop :=
  ∀ a∈sectorReads p, E1M1LineLoad.CopySafe a address ∧ Apart a (address+46) ∧ Apart a (address+50)
def reads (address : Word) (p : Portal) : List Word :=
  (address+16)::E1M1OpeningHeights.reads address p.front p.back

theorem pointers (e : OriginalGroupOutput.Line) (s : X86Memory.State)
    (source : E1M1LineLoad.Source e s) :
    load32 (OriginalLineLoad.result s).core.memory (e.address+46)=e.front ∧
    load32 (OriginalLineLoad.result s).core.memory (e.address+50)=e.back := by
  obtain ⟨out,run,image,_⟩ := E1M1LineLoad.establishes e s none source
  rw [OriginalLineLoad.joined_execution] at run
  have same := Option.some.inj run
  subst out
  exact image e (by simp)

/-- The back index is copied from raw input and survives both cached stores. -/
theorem back_index (e : OriginalGroupOutput.Line) (s : X86Memory.State)
    (source : E1M1LineLoad.Source e s) :
    load16 (OriginalLineLoad.result s).core.memory (e.address+24)=source.backIndex := by
  have second : OriginalLineLoad.second s=source.backIndex := by
    unfold OriginalLineLoad.second OriginalLineLoad.firstMemory
    rw [HalfMemory.half_frame _ _ _ _ (by simpa only [source.line] using source.nextRead)]
    exact source.backRead
  have copied := (OriginalLineLoad.copied_indices s).2
  rw [second,source.line] at copied
  have apart (off : Word) (member : off∈[(46#32),50]) : Apart (e.address+24) (e.address+off) := by
    apply OriginalPathXStep.apart_translate
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> unfold Apart <;> decide
  rw [(OriginalLineLoad.progress s).1]
  have frame := OriginalLineCache.frame (OriginalLineLoad.copied s) (e.address+24)
    (by simpa only [OriginalLineLoad.copied_reg s 3 (by decide),source.line] using apart 46 (by simp))
    (by simpa only [OriginalLineLoad.copied_reg s 3 (by decide),source.line] using apart 50 (by simp))
  exact (E1M1NoiseGraph.load16_of_word frame).trans copied

/-- Neither the two halfword copies nor the pointer stores change line flags. -/
theorem flags (s : X86Memory.State) :
    (OriginalLineLoad.result s).core.memory (s.regs 3+16)=s.memory (s.regs 3+16) := by
  apply E1M1NoiseGraph.byte_of_word
  apply E1M1LineLoad.frame
  · constructor <;> apply HalfMemory.translate <;> unfold HalfMemory.Separate <;> decide
  · apply OriginalPathXStep.apart_translate; unfold Apart; decide
  · apply OriginalPathXStep.apart_translate; unfold Apart; decide

theorem sectors (address : Word) (p : Portal) (s : X86Memory.State)
    (position : s.regs 3=address) (safe : SectorSafe address p) (values : SectorValues s.memory p) :
    SectorValues (OriginalLineLoad.result s).core.memory p := by
  have keep (a : Word) (ha : a∈sectorReads p) :
      load32 (OriginalLineLoad.result s).core.memory a=load32 s.memory a := by
    have guard := safe a ha
    exact E1M1LineLoad.frame s a (by simpa only [position] using guard.1)
      (by simpa only [position] using guard.2.1) (by simpa only [position] using guard.2.2)
  exact ⟨(keep _ (by simp [sectorReads])).trans values.1,
    (keep _ (by simp [sectorReads])).trans values.2.1,
    (keep _ (by simp [sectorReads])).trans values.2.2.1,
    (keep _ (by simp [sectorReads])).trans values.2.2.2⟩

/-- Aiming's full opening image follows from the actual loader suffix.
Side presence and preexisting sector heights remain input facts. -/
theorem image (address : Word) (p : Portal) (s : X86Memory.State)
    (source : E1M1LineLoad.Source (line address p) s) (present : source.backIndex≠0xffff)
    (safe : SectorSafe address p) (values : SectorValues s.memory p) :
    E1M1AimOpeningFrame.Image (OriginalLineLoad.result s).core.memory address
      p.front p.back p.ff p.fc p.bf p.bc := by
  have ptrs := pointers (line address p) s source
  have heights := sectors address p s source.line safe values
  have index : load16 (OriginalLineLoad.result s).core.memory (address+24)=source.backIndex :=
    back_index (line address p) s source
  exact ⟨fun eq => present (index.symm.trans eq),
    ptrs.1,ptrs.2,heights.1,heights.2.1,heights.2.2.1,heights.2.2.2⟩

theorem values (address : Word) (p : Portal) (s : X86Memory.State) (hit : Intercept)
    (source : E1M1LineLoad.Source (line address p) s) (present : source.backIndex≠0xffff)
    (safe : SectorSafe address p) (heights : SectorValues s.memory p)
    (kind : hit.isLine=true) (two : s.memory (address+16) &&& (4#8)≠0) :
    E1M1AimObjectCatalog.PortalValues (OriginalLineLoad.result s).core.memory hit address p := by
  refine ⟨kind,image address p s source present safe heights,?_⟩
  have kept := flags s
  rw [source.line] at kept
  simp only [line] at kept
  rw [kept]; exact two

/-- A solid wall needs no back-sector image or non-sentinel back index. -/
theorem wall (s : X86Memory.State) (hit : Intercept) (kind : hit.isLine=true)
    (solid : s.memory (s.regs 3+16) &&& (4#8)=0) :
    E1M1AimObjectCatalog.WallValues (OriginalLineLoad.result s).core.memory hit (s.regs 3) := by
  exact ⟨kind,by rw [flags]; exact solid⟩

/-- Transport only the eight read words, including the flags byte and back-side
halfword. This does not assume equality of all loader and aiming memory. -/
theorem transport (before after : Memory) (hit : Intercept) (address : Word) (p : Portal)
    (initial : E1M1AimObjectCatalog.PortalValues before hit address p)
    (frame : ∀ a∈reads address p, load32 after a=load32 before a) :
    E1M1AimObjectCatalog.PortalValues after hit address p := by
  have keep (a : Word) (ha : a∈E1M1OpeningHeights.reads address p.front p.back) :=
    frame a (List.mem_cons_of_mem _ ha)
  refine ⟨initial.1,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [E1M1NoiseGraph.load16_of_word (keep _ (by simp [E1M1OpeningHeights.reads]))]; exact initial.2.1.side
  · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans initial.2.1.frontPtr
  · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans initial.2.1.backPtr
  · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans initial.2.1.frontFloor
  · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans initial.2.1.frontCeiling
  · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans initial.2.1.backFloor
  · exact (keep _ (by simp [E1M1OpeningHeights.reads])).trans initial.2.1.backCeiling
  · rw [E1M1NoiseGraph.byte_of_word (frame _ (by simp [reads]))]; exact initial.2.2

/-- Join the established loader output to a later aiming catalog. The read
frame across intervening execution and actual storage placement are explicit. -/
theorem catalog (address : Word) (p : Portal) (s aim : X86Memory.State) (hit : Intercept)
    (source : E1M1LineLoad.Source (line address p) s) (present : source.backIndex≠0xffff)
    (safe : SectorSafe address p) (heights : SectorValues s.memory p)
    (kind : hit.isLine=true) (two : s.memory (address+16) &&& (4#8)≠0)
    (frame : ∀ a∈reads address p, load32 aim.memory a=load32 (OriginalLineLoad.result s).core.memory a)
    (stack : Region) (sp : Word) (reserve : E1M1AimWalkRegions.Reserve stack sp)
    (position : aim.regs 4=sp-140)
    (lineStorage : E1M1AimObjectRegions.Storage stack address 62)
    (frontStorage : E1M1AimObjectRegions.Storage stack p.front 8)
    (backStorage : E1M1AimObjectRegions.Storage stack p.back 8) :
    E1M1AimCatalog.Entry aim hit address p := by
  exact E1M1AimObjectCatalog.portal stack sp aim hit address p lineStorage frontStorage backStorage reserve position
    (transport _ _ hit address p (values address p s hit source present safe heights kind two) frame)

/-- The same proved output belongs to the uninterrupted original copy/cache/
advance execution, not just to a separately postulated decoded memory image. -/
theorem execution (address : Word) (p : Portal) (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (source : E1M1LineLoad.Source (line address p) s) (present : source.backIndex≠0xffff)
    (safe : SectorSafe address p) (heights : SectorValues s.memory p)
    (kind : hit.isLine=true) (two : s.memory (address+16) &&& (4#8)≠0) :
    X86Routine.run OriginalLineLoad.program [0x2e29a,0x2e3c1] 26 ⟨s,f,0x2e358⟩=some (OriginalLineLoad.result s) ∧
    E1M1AimObjectCatalog.PortalValues (OriginalLineLoad.result s).core.memory hit address p := by
  exact ⟨OriginalLineLoad.joined_execution s f,values address p s hit source present safe heights kind two⟩
end Doom.Proofs.E1M1AimLoadedPortal

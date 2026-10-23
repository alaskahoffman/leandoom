import Doom.Proofs.E1M1AimLoadedScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimInitialPortal
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1LineScan (cursor states)

/-- The portal's pointer identity is the initial side image's identity. -/
def portal (e : E1M1LineOutput.Sides) (ff fc bf bc : Word) : E1M1AimCatalog.Portal :=
  ⟨e.front,e.back,ff,fc,bf,bc⟩

/-- Reuse source-image preservation and the existing copy-source constructor.
No reached raw-side or side-table image is assumed here. -/
theorem source_at_copy (total : Nat) (records : Fin total → E1M1LineOutput.Sides)
    (raw sideBase base sp : Word) (s : X86Memory.State) (f : Option Flags) (i : Fin total)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (separate : E1M1LineOutput.ImageLayout records raw sideBase base sp)
    (image : E1M1LineOutput.Image records raw sideBase s.memory) :
    ∃ source : E1M1LineLoad.Source (E1M1LineOutput.line (records i) (cursor base 62 i.val))
        (E1M1LineOutput.copyInput (states s f i.val).core),
      source.backIndex=(records i).backIndex := by
  have current := (E1M1LineScan.states_ready (f:=f) loop ready i.val (by omega)).1
  have before := E1M1LineOutput.image_preserved (f:=f) loop ready separate image i.val (by omega) i
  rw [←current.output]
  exact ⟨E1M1LineOutput.copy_source (records i) sideBase (states s f i.val).core
    (by rw [current.source]; exact before)
    (by rw [current.source,current.output,current.stack]; exact separate i i),rfl⟩

/-- A sector word survives both earlier complete records and the current
record's metadata/geometry prefix. The existing byte frames do all the work. -/
theorem sector_word_at_copy (total : Nat) (raw base sp address : Word) (stack : Region)
    (s : X86Memory.State) (f : Option Flags) (i : Fin total) (off : Nat)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (sector : E1M1AimLoadedScanRegions.Sector total base address stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp) (fits : off+4≤8) :
    load32 (E1M1LineOutput.copyInput (states s f i.val).core).memory (address+BitVec.ofNat 32 off)=
      load32 s.memory (address+BitVec.ofNat 32 off) := by
  have current := (E1M1LineScan.states_ready (f:=f) loop ready i.val (by omega)).1
  have earlier := E1M1LineScan.suffix_frame (s:=s) (f:=f) loop ready
    (address+BitVec.ofNat 32 off) 0 i.val (by omega) (fun j _ upper =>
      E1M1AimLoadedScanRegions.sector_field total base address sp stack j off
        layout sector reserve (by omega) fits)
  simp only [Nat.zero_add] at earlier
  have kept := E1M1LineOutput.copy_frame (states s f i.val).core (address+BitVec.ofNat 32 off) (by
    rw [current.output,current.stack]
    exact E1M1AimLoadedScanRegions.sector_field total base address sp stack i.val off
      layout sector reserve i.isLt fits)
  exact kept.trans earlier

theorem sectors_at_copy (total : Nat) (raw base sp : Word) (stack : Region)
    (s : X86Memory.State) (f : Option Flags) (i : Fin total) (p : E1M1AimCatalog.Portal)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base p.front stack)
    (back : E1M1AimLoadedScanRegions.Sector total base p.back stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp)
    (initial : E1M1AimLoadedPortal.SectorValues s.memory p) :
    E1M1AimLoadedPortal.SectorValues (E1M1LineOutput.copyInput (states s f i.val).core).memory p := by
  have ff := sector_word_at_copy total raw base sp p.front stack s f i 0 loop ready layout front reserve (by decide)
  have fc := sector_word_at_copy total raw base sp p.front stack s f i 4 loop ready layout front reserve (by decide)
  have bf := sector_word_at_copy total raw base sp p.back stack s f i 0 loop ready layout back reserve (by decide)
  have bc := sector_word_at_copy total raw base sp p.back stack s f i 4 loop ready layout back reserve (by decide)
  simp only [BitVec.add_zero] at ff bf
  exact ⟨ff.trans initial.1,fc.trans initial.2.1,bf.trans initial.2.2.1,bc.trans initial.2.2.2⟩

/-- Replace reached side/height assumptions by the initial loader images.
The two-sided flag remains a reached-prefix premise, explicitly visible below. -/
theorem established (total : Nat) (records : Fin total → E1M1LineOutput.Sides)
    (raw sideBase base sp : Word) (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (i : Fin total) (hit : Intercept) (ff fc bf bc : Word)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (separate : E1M1LineOutput.ImageLayout records raw sideBase base sp)
    (image : E1M1LineOutput.Image records raw sideBase s.memory)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base (records i).front stack)
    (back : E1M1AimLoadedScanRegions.Sector total base (records i).back stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp)
    (present : (records i).backIndex≠0xffff)
    (heights : E1M1AimLoadedPortal.SectorValues s.memory (portal (records i) ff fc bf bc))
    (kind : hit.isLine=true)
    (two : (E1M1LineOutput.copyInput (states s f i.val).core).memory (cursor base 62 i.val+16) &&& (4#8)≠0) :
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i.val)
      (portal (records i) ff fc bf bc) := by
  obtain ⟨source,index⟩ := source_at_copy total records raw sideBase base sp s f i loop ready separate image
  exact E1M1AimLoadedScan.established total raw base sp stack s f i.val hit
    (portal (records i) ff fc bf bc) loop ready layout front back reserve i.isLt source
    (fun eq => present (index.symm.trans eq))
    (sectors_at_copy total raw base sp stack s f i _ loop ready layout front back reserve heights) kind two

/-- Reuse the earlier geometry-image arithmetic theorem instead of assuming
successful arithmetic at every reached iteration. Initial representation,
finite geometry safety, separation and the reached flag still remain premises. -/
theorem execution_from_image (total : Nat) (records : Fin total → E1M1LineOutput.Sides)
    (geometry : Fin total → E1M1LineSource.Record) (raw sideBase vertexBase base sp : Word)
    (stack : Region) (s : X86Memory.State) (f : Option Flags) (i : Fin total)
    (hit : Intercept) (ff fc bf bc : Word)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (verticesSafe : E1M1LineSource.ImageLayout geometry raw vertexBase base sp)
    (vertices : E1M1LineSource.Image geometry raw vertexBase s.memory)
    (good : ∀ j, E1M1LineSource.good (geometry j)=true)
    (separate : E1M1LineOutput.ImageLayout records raw sideBase base sp)
    (image : E1M1LineOutput.Image records raw sideBase s.memory)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base (records i).front stack)
    (back : E1M1AimLoadedScanRegions.Sector total base (records i).back stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp)
    (present : (records i).backIndex≠0xffff)
    (heights : E1M1AimLoadedPortal.SectorValues s.memory (portal (records i) ff fc bf bc))
    (kind : hit.isLine=true)
    (two : (E1M1LineOutput.copyInput (states s f i.val).core).memory (cursor base 62 i.val+16) &&& (4#8)≠0) :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=some (states s f total) ∧
    (states s f total).pc=0x2e3c1 ∧
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i.val)
      (portal (records i) ff fc bf bc) := by
  have run := E1M1LineSource.scan_from_image (f:=f) loop ready verticesSafe vertices good
    (by have := i.isLt; omega)
  exact ⟨run.1,run.2.1,established total records raw sideBase base sp stack s f i hit ff fc bf bc
    loop ready separate image layout front back reserve present heights kind two⟩
end Doom.Proofs.E1M1AimInitialPortal

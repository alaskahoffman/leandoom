import Doom.Proofs.E1M1AimLoadedScanRegions
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimLoadedScan
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1AimCatalog (Portal)
open E1M1LineScan (cursor states)

/-- The suffix output is the actual complete iteration output, not a second
execution started with an unrelated machine state. -/
theorem iteration_suffix (s : X86Memory.State) :
    E1M1LineIteration.result s=OriginalLineLoad.result (E1M1LineOutput.copyInput s) := by
  rw [E1M1LineFrame.result_eq]
  rfl

/-- Carry a portal established at iteration i through every remaining record. -/
theorem retained (total : Nat) (raw base sp : Word) (stack : Region)
    (s : X86Memory.State) (f : Option Flags) (i : Nat) (hit : Intercept) (p : Portal)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base p.front stack)
    (back : E1M1AimLoadedScanRegions.Sector total base p.back stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp) (inside : i<total)
    (initial : E1M1AimObjectCatalog.PortalValues (states s f (i+1)).core.memory hit (cursor base 62 i) p) :
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i) p := by
  apply E1M1AimLoadedPortal.transport _ _ hit (cursor base 62 i) p initial
  intro a member
  have keep := E1M1LineScan.suffix_frame (s:=s) (f:=f) loop ready a (i+1) (total-(i+1))
    (by omega) (fun j lower upper =>
      E1M1AimLoadedScanRegions.portal_reads total base sp stack i j p layout front back reserve
        (by omega) (by omega) a member)
  have done : i+1+(total-(i+1))=total := by omega
  rw [done] at keep
  exact keep

/-- Start with raw side-copy inputs at the reached suffix and derive the final
portal. Later iterations need no assumed memory equality or portal images. -/
theorem established (total : Nat) (raw base sp : Word) (stack : Region)
    (s : X86Memory.State) (f : Option Flags) (i : Nat) (hit : Intercept) (p : Portal)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base p.front stack)
    (back : E1M1AimLoadedScanRegions.Sector total base p.back stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp) (inside : i<total)
    (source : E1M1LineLoad.Source (E1M1AimLoadedPortal.line (cursor base 62 i) p)
      (E1M1LineOutput.copyInput (states s f i).core))
    (present : source.backIndex≠0xffff)
    (heights : E1M1AimLoadedPortal.SectorValues (E1M1LineOutput.copyInput (states s f i).core).memory p)
    (kind : hit.isLine=true)
    (two : (E1M1LineOutput.copyInput (states s f i).core).memory (cursor base 62 i+16) &&& (4#8)≠0) :
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i) p := by
  apply retained total raw base sp stack s f i hit p loop ready layout front back reserve inside
  rw [states,iteration_suffix]
  exact E1M1AimLoadedPortal.values _ p _ hit source present
    (E1M1AimLoadedScanRegions.sector_safe total base sp stack i p layout front back reserve inside)
    heights kind two

/-- The portal belongs to the uninterrupted positive-count machine-code loop.
Per-iteration arithmetic, initial registers/count and source contents remain
explicit. This does not claim a theorem about all of DOS startup. -/
theorem execution (total : Nat) (raw base sp : Word) (stack : Region)
    (s : X86Memory.State) (f : Option Flags) (i : Nat) (hit : Intercept) (p : Portal)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (arithmetic : E1M1LineScan.Arithmetic total s f)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base p.front stack)
    (back : E1M1AimLoadedScanRegions.Sector total base p.back stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp) (inside : i<total)
    (source : E1M1LineLoad.Source (E1M1AimLoadedPortal.line (cursor base 62 i) p)
      (E1M1LineOutput.copyInput (states s f i).core))
    (present : source.backIndex≠0xffff)
    (heights : E1M1AimLoadedPortal.SectorValues (E1M1LineOutput.copyInput (states s f i).core).memory p)
    (kind : hit.isLine=true)
    (two : (E1M1LineOutput.copyInput (states s f i).core).memory (cursor base 62 i+16) &&& (4#8)≠0) :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=some (states s f total) ∧
    (states s f total).pc=0x2e3c1 ∧
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i) p := by
  have run := E1M1LineScan.scan_execution loop ready arithmetic (by omega)
  exact ⟨run.1,run.2.1,established total raw base sp stack s f i hit p loop ready
    layout front back reserve inside source present heights kind two⟩
end Doom.Proofs.E1M1AimLoadedScan

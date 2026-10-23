import Doom.Proofs.E1M1AimLoaderFlags
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimRawPortal
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1LineScan (cursor states)
open E1M1AimInitialPortal (portal)

/-- The existing array and stack bounds protect the current flag word from
all four possible stack writes. No disjointness from its own metadata store. -/
theorem flag_stack (total : Nat) (base sp : Word) (stack : Region) (i : Fin total)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp) :
    ∀ off∈[(4#32),8,12,16], Apart (cursor base 62 i.val+16) (sp-off) := by
  have read := E1M1AimLoadedScanRegions.record_field total base i.val 16 layout.bound i.isLt (by decide)
  have saved (n : Nat) (low : 4≤n) (high : n≤16) : stack.Contains (sp-BitVec.ofNat 32 n) := by
    have size := sp.isLt
    simp only [E1M1AimLoadedScanRegions.Reserve] at reserve
    simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
    omega
  intro off member
  apply Region.apart read ?_ layout.stackApart
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> exact saved _ (by decide) (by decide)

/-- Earlier iterations preserve the raw flag, then the current metadata copy
and geometry prefix establish its exact output byte. No reached flag premise. -/
theorem flag_at_copy (total : Nat) (raw base sp : Word) (stack : Region)
    (s : X86Memory.State) (f : Option Flags) (i : Fin total)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp)
    (flagSourceSafe : ∀ j, j<i.val → E1M1LineFrame.Protected
      (cursor raw 14 i.val+4) (cursor base 62 j) sp) :
    (E1M1LineOutput.copyInput (states s f i.val).core).memory (cursor base 62 i.val+16)=
      s.memory (cursor raw 14 i.val+4) := by
  have current := (E1M1LineScan.states_ready (f:=f) loop ready i.val (by omega)).1
  have earlier := E1M1LineScan.suffix_frame (s:=s) (f:=f) loop ready (cursor raw 14 i.val+4) 0 i.val
    (by omega) (fun j _ hi => flagSourceSafe j (by omega))
  simp only [Nat.zero_add] at earlier
  have copied := E1M1AimLoaderFlags.flag_byte (states s f i.val).core (by
    rw [current.output,current.stack]; exact flag_stack total base sp stack i layout reserve)
  rw [current.output,current.source] at copied
  exact copied.trans (E1M1NoiseGraph.byte_of_word earlier)

/-- All portal content premises are now at the initial line-loop state.
Initial representations, placement and finite geometry safety remain required. -/
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
    (flagSourceSafe : ∀ j, j<i.val → E1M1LineFrame.Protected
      (cursor raw 14 i.val+4) (cursor base 62 j) sp)
    (two : s.memory (cursor raw 14 i.val+4) &&& (4#8)≠0) :
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i.val)
      (portal (records i) ff fc bf bc) := by
  apply E1M1AimInitialPortal.established total records raw sideBase base sp stack s f i hit ff fc bf bc loop ready separate image layout front back reserve present heights kind
  rw [flag_at_copy total raw base sp stack s f i loop ready layout reserve flagSourceSafe]
  exact two

/-- All portal content premises are now at the initial line-loop state.
Initial representations, placement and finite geometry safety remain required. -/
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
    (flagSourceSafe : ∀ j, j<i.val → E1M1LineFrame.Protected
      (cursor raw 14 i.val+4) (cursor base 62 j) sp)
    (two : s.memory (cursor raw 14 i.val+4) &&& (4#8)≠0) :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=some (states s f total) ∧
    (states s f total).pc=0x2e3c1 ∧
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i.val)
      (portal (records i) ff fc bf bc) := by
  apply E1M1AimInitialPortal.execution_from_image total records geometry raw sideBase vertexBase base sp stack s f i hit ff fc bf bc loop ready verticesSafe vertices good separate image layout front back reserve present heights kind
  rw [flag_at_copy total raw base sp stack s f i loop ready layout reserve flagSourceSafe]
  exact two
end Doom.Proofs.E1M1AimRawPortal

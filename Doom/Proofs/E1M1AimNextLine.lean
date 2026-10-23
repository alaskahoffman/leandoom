import Doom.Proofs.E1M1AimMapFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimNextLine
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCycleInvariant (Layout QuerySafe)
open E1M1AimMapFrame (Region)
attribute [local irreducible] load32 store32

/-- Separation for globals read after floor clipping. Their values need not
be read-only: the opening helper produces 0x2c034 and aiming updates its bounds. -/
def ClipGlobalsSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [(0x2c034#32),(0x2b9a8#32),(0x2c1e8#32)]
    (E1M1AimClipFrame.writes (s.regs 4-(24#32)))

theorem clip_globals (s t : X86Memory.State) (stack : t.regs 4=s.regs 4)
    (safe : ClipGlobalsSafe s) : ClipGlobalsSafe t := by
  simpa only [ClipGlobalsSafe,stack] using safe

/-- Next-line map addresses use the persistent region protection, while the
three helper/query globals retain their separate fixed-layout condition. -/
theorem clip_safe (s : X86Memory.State) (line front back : Word)
    (safe : Region s line front back) (globals : ClipGlobalsSafe s) :
    E1M1AimCeilingEntry.ClipSafe s line front back := by
  intro a member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact E1M1AimMapFrame.floor_safe s _ (safe _ (by simp [E1M1OpeningHeights.reads])).1
  · exact E1M1AimMapFrame.floor_safe s _ (safe _ (by simp [E1M1OpeningHeights.reads])).1
  · exact E1M1AimMapFrame.floor_safe s _ (safe _ (by simp [E1M1OpeningHeights.reads])).1
  · exact E1M1AimMapFrame.floor_safe s _ (safe _ (by simp [E1M1OpeningHeights.reads])).1
  · exact globals _ (by simp)
  · exact globals _ (by simp)
  · exact globals _ (by simp)

/-- The newly selected fraction and unchanged attack range survive the next
opening helper. The fraction address comes from the reached selection. -/
theorem distance_reads (s : X86Control.State) (initial work : Array Intercept)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (target sp : Word) (distance : Int32) (j : Nat)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp s distance j)
    (records : E1M1AimRecordFrame.RecordsSafe s.core work) (querySafe : QuerySafe s.core) :
    E1M1AimDistance.ReadSafe s.core := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have fraction := records j inside (0#32) (by simp)
  have fraction' : E1M1AimRecordFrame.ReadSafe s.core (s.core.regs 0) := by
    rw [selection.argument]
    simpa only [BitVec.add_zero] using fraction
  intro a member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  · exact E1M1AimMapFrame.opening_safe s.core _ fraction'
  · exact E1M1AimMapFrame.opening_safe s.core _ (querySafe _ (by simp)).1

/-- Assemble the actual next callback's full mapped-line inputs. The next
memory image, byte flags, pointer-dependent separation and arithmetic-read
conditions are derived from pre-cycle data and the reached selected record. -/
theorem entry (s : X86Memory.State) (initial hits : Array Intercept) (marked : Nat)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (target : Word) (out : X86Control.State) (distance : Int32) (j : Nat)
    (history : History initial (consume hits marked) seen visits)
    (selection : Selection initial (consume hits marked) seen resolve target (s.regs 4+4) out distance j)
    (bounded : initial.size≤128) (safe : Layout s hits) (querySafe : QuerySafe s)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (markBound : marked<128)
    (front back ff fc bf bc : Word)
    (mapRegion : Region s (resolve initial[j]!) front back)
    (mapImage : E1M1AimOpeningFrame.Image s.memory (resolve initial[j]!) front back ff fc bf bc)
    (isLine : initial[j]!.isLine=true)
    (two : s.memory (resolve initial[j]!+(16#32)) &&& (4#8)≠0)
    (globals : ClipGlobalsSafe s) :
    E1M1AimMapped.Inputs out.core (consume hits marked)[j]! (resolve initial[j]!) front back ff fc bf bc ∧
    E1M1AimDistance.ReadSafe out.core ∧
    E1M1AimCeilingEntry.ClipSafe out.core (resolve initial[j]!) front back ∧
    Region out.core (resolve initial[j]!) front back ∧ ClipGlobalsSafe out.core := by
  obtain ⟨stack,layout,query,record,range,eye⟩ := E1M1AimCycleInvariant.entry s initial hits marked seen visits
    resolve target out distance j history selection bounded safe querySafe frame
  have region := E1M1AimMapFrame.region s out.core (resolve initial[j]!) front back stack mapRegion
  have image := E1M1AimMapFrame.image s out marked (resolve initial[j]!) front back ff fc bf bc
    frame pointer markBound mapRegion mapImage
  have global := clip_globals s out.core stack globals
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<(consume hits marked).size := by have := selection.inside; omega
  have tag : E1M1AimWall.Safe (out.core.regs 4) (out.core.regs 0+4) := by
    rw [selection.argument]
    exact (layout.recordsSafe j inside 4 (by simp)).1
  have ptr : E1M1AimWall.Safe (out.core.regs 4) (out.core.regs 0+8) := by
    rw [selection.argument]
    exact (layout.recordsSafe j inside 8 (by simp)).1
  refine ⟨?_,?_,clip_safe out.core _ front back region global,region,global⟩
  · rw [selection.original]
    exact ⟨record,isLine,tag,ptr,(region _ (by simp)).1.1,
      (by change out.core.memory (resolve initial[j]!+(16#32)) &&& (4#8)≠0
          rw [image.2]; exact two),layout.helperSafe,
      E1M1AimMapFrame.map_safe out.core _ front back region,image.1⟩
  · exact distance_reads out initial (consume hits marked) seen visits resolve target (s.regs 4+4)
      distance j history selection layout.recordsSafe query
end Doom.Proofs.E1M1AimNextLine

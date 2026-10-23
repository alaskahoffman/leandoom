import Doom.Proofs.E1M1NextCellMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1NextCellScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NextCellMemory (advanced scan Safe)
open E1M1PathAdvance (Cell observe step nextPc)
abbrev program := E1M1FiringAdvance.program
attribute [local irreducible] load32

/-- Reuse the already authenticated caller, bounds and lookup instructions in
the same program as the firing prefix. No new machine-code range is added. -/
theorem contains_caller (pc : Nat) (h : E1M1PathMapCaller.program pc≠none) :
    program pc=E1M1PathMapCaller.program pc := by
  by_cases dispatch : 0x2ca7f≤pc ∧ pc<0x2cab5
  · have all : ∀ i : Fin 54, program (0x2ca7f+i.val)=E1M1PathMapCaller.program (0x2ca7f+i.val) := by decide +kernel
    have eq : 0x2ca7f+(pc-0x2ca7f)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2ca7f,by omega⟩
  · have range : 0x2c520≤pc ∧ pc<0x2c591 := by
      by_cases r : 0x2c520≤pc ∧ pc<0x2c591
      · exact r
      · have a : ¬(0x2c520≤pc ∧ pc<0x2c541) := by omega
        have b : ¬(0x2c587≤pc ∧ pc<0x2c591) := by omega
        have c : ¬(0x2c541≤pc ∧ pc<0x2c587) := by omega
        simp [E1M1PathMapCaller.program,E1M1PathMapCaller.bytesProgram,
          OriginalPathCell.bytesProgram,dispatch,E1M1PathMapBounds.bytesProgram,
          OriginalLineBounds.bytesProgram,OriginalLineCell.bytesProgram,a,b,c] at h
    have all : ∀ i : Fin 113, program (0x2c520+i.val)=E1M1PathMapCaller.program (0x2c520+i.val) := by decide +kernel
    have eq : 0x2c520+(pc-0x2c520)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c520,by omega⟩

/-- Execute an arbitrary continuing grid step and the next in-map cell lookup.
Coordinates come from the proved numeric step; all memory premises are before
that step. This stops before visiting the next cell's first line. -/
theorem inside (s : X86Memory.State) (f : Option Flags) (g : Cell)
    (observed : observe s=g) (next : nextPc g=0x2ca7f)
    (x y : Int32) (mapX : (step g).mapX=x.toBitVec) (mapY : (step g).mapY=y.toBitVec)
    (base lines : Word) (words : Array Nat) (c : E1M1PathMap.Cell) (w h : Nat)
    (enabled : OriginalPathCell.enabled true s=true)
    (dims : E1M1PathMapCaller.Dimensions s w h)
    (globals : E1M1PathMapCaller.Globals s base lines)
    (encoded : E1M1PathMap.WordImage s.memory base words)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Apart a (s.regs 4+(44#32)))
    (imageSafe : ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i)))
    (inMap : Collision.pathCellInside x y w h=true) (valid : c.Valid words)
    (selected : words[4+Collision.pathCellIndex x y w]?=some c.offset) :
    (∃ n≤49, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2cab5⟩ (scan s)) ∧
    E1M1PathMapLookup.ScanWords (scan s).core lines c ∧
    (scan s).pc=0x2c57f ∧ (scan s).core.regs 4=s.regs 4-(12#32) := by
  obtain ⟨⟨a,ha,advance⟩,obs,pc,sp⟩ := E1M1PathAdvance.execution s f
  rw [observed] at obs pc
  have state := E1M1NextCellMemory.map s base lines words w h dims globals encoded globalsSafe imageSafe
  have enabled' := (E1M1NextCellMemory.enabled s true).trans enabled
  have xcoord := (congrArg Cell.mapX obs).trans mapX
  have ycoord := (congrArg Cell.mapY obs).trans mapY
  obtain ⟨⟨b,hb,lookup⟩,items,stop,stack⟩ := E1M1PathMapCaller.inside_to_scan
    (advanced s) (OriginalPathAdvance.result s).flags base lines words c x y w h
    enabled' state.1 xcoord ycoord state.2.1 inMap valid state.2.2.1 state.2.2.2 selected
  rw [OriginalPathXStep.at_pc _ _ (pc.trans next)] at lookup
  exact ⟨⟨a+b,by omega,E1M1PspriteStep.prefix_trans
    (X86CodeMemory.lift_success (advance.transfer program [] E1M1FiringAdvance.contains_advance (by simp)) FloorCaller.cm)
    (X86CodeMemory.lift_success (lookup.transfer program [] contains_caller (by simp)) FloorCaller.cm)⟩,
    items,stop,stack.trans (congrArg (fun v : Word => v-(12#32)) sp)⟩

/-- An out-of-map next cell reaches the thing gate after the real line iterator
returns success. No BLOCKMAP contents, line IDs or callback result are needed. -/
theorem outside (s : X86Memory.State) (f : Option Flags) (g : Cell)
    (observed : observe s=g) (next : nextPc g=0x2ca7f)
    (x y : Int32) (mapX : (step g).mapX=x.toBitVec) (mapY : (step g).mapY=y.toBitVec)
    (w h : Nat) (enabled : OriginalPathCell.enabled true s=true)
    (dims : E1M1PathMapCaller.Dimensions s w h)
    (safe : ∀ a∈[(0x2c0fc#32),0x2c110], Apart a (s.regs 4+(44#32)))
    (outMap : Collision.pathCellInside x y w h=false) :
    let out := E1M1PathMapCaller.resumed (advanced s)
    (∃ n≤43, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2cab5⟩ out) ∧
    out.pc=0x2ca9c ∧ out.core.regs 4=s.regs 4 ∧ out.core.regs 0=1 := by
  obtain ⟨⟨a,ha,advance⟩,obs,pc,sp⟩ := E1M1PathAdvance.execution s f
  rw [observed] at obs pc
  have retained : E1M1PathMapCaller.Dimensions (advanced s) w h :=
    ⟨(E1M1AdvanceCollection.frame s _ (safe _ (by simp))).trans dims.width,
      (E1M1AdvanceCollection.frame s _ (safe _ (by simp))).trans dims.height,
      dims.widthBound,dims.heightBound,
      fun a ha => E1M1NextCellMemory.caller_safe s a (dims.safe a ha)⟩
  obtain ⟨⟨b,hb,lookup⟩,stop,stack,value⟩ := E1M1PathMapCaller.outside_to_things
    (advanced s) (OriginalPathAdvance.result s).flags x y w h
    ((E1M1NextCellMemory.enabled s true).trans enabled) retained
    ((congrArg Cell.mapX obs).trans mapX) ((congrArg Cell.mapY obs).trans mapY) outMap
  rw [OriginalPathXStep.at_pc _ _ (pc.trans next)] at lookup
  exact ⟨⟨a+b,by omega,E1M1PspriteStep.prefix_trans
    (X86CodeMemory.lift_success (advance.transfer program [] E1M1FiringAdvance.contains_advance (by simp)) FloorCaller.cm)
    (X86CodeMemory.lift_success (lookup.transfer program [] contains_caller (by simp)) FloorCaller.cm)⟩,
    stop,stack.trans sp,value⟩

/-- All mutable scan inputs travel together to the reached scan entry. The
reserve is unchanged; zero reserve does not justify scanning another cell. -/
theorem scan_invariants (s : X86Memory.State) (lines epoch : Word) (seen : Array Bool)
    (represented : OriginalLineVisits.Represents s.memory lines epoch seen)
    (epochSafe : Safe s (0x13580#32))
    (stampsSafe : ∀ j<seen.size, Safe s (OriginalLineVisits.stamp lines j))
    (base : Word) (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept)
    (reserve : Nat) (tracked : OriginalLineCollection.Tracks s base resolve hits reserve)
    (advanceSafe : OriginalLineMixedInvariant.ArraySafe base (s.regs 4+(44#32)))
    (cursorSafe : E1M1PathMapCaller.Safe s (0x2c028#32))
    (recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      E1M1PathMapCaller.Safe s (OriginalLineCollection.slot base i off)) :
    OriginalLineVisits.Represents (scan s).core.memory lines epoch seen ∧
    OriginalLineCollection.Tracks (scan s).core base resolve hits reserve :=
  ⟨E1M1NextCellMemory.visits s lines epoch seen represented epochSafe stampsSafe,
    E1M1NextCellMemory.collection s base resolve hits reserve tracked advanceSafe cursorSafe recordsSafe⟩
end Doom.Proofs.E1M1NextCellScan

import Doom.Proofs.OriginalGroupOutput
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1GroupOutput
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseTopology
open OriginalGroupStep OriginalGroupScan OriginalGroupOutput

def physical (a : Addresses) (e : E1M1NoiseTopology.Line) : OriginalGroupOutput.Line :=
  ⟨a.line e.index,a.sector e.front,OriginalGroupLines.backAddress e a⟩

theorem physical_chosen (a : Addresses) (sector : Word) (lines : List E1M1NoiseTopology.Line) :
    chosen sector (lines.map (physical a))=
      ((lines.filter fun e => OriginalGroupLines.accepts sector (a.sector e.front) (OriginalGroupLines.backAddress e a)).map E1M1NoiseTopology.Line.index).map a.line := by
  simp [chosen,physical,List.filter_map,List.map_map,Function.comp_def]

/-- The actual output specification equals the pinned map's ordered sector row,
including absent back sectors and self-referencing lines. -/
theorem ordered_row (t : Topology) (a : Addresses)
    (layout : OriginalGroupLines.SectorAddresses a t.sectors.length)
    (ranges : ∀ e∈t.lines, OriginalGroupLines.InRange e t.sectors.length)
    (grouped : t.Grouped) (i : Fin t.sectors.length) :
    chosen (a.sector i.val) (t.lines.map (physical a))=(t.sectors[i.val]).map a.line := by
  rw [physical_chosen,OriginalGroupLines.ordered_selection t a layout ranges grouped i]

/-- Initial memory and finite physical storage requirements, not an assumed
output array or post-execution MapRep. The count field originates in the still
separate counting pass. Front/back pointers originate in cached-line loading. -/
structure Setup (t : Topology) (a : Addresses) (i : Fin t.sectors.length) (s : X86Memory.State) : Prop where
  sector : s.regs 5=a.sector i.val
  array : s.regs 6=a.array i.val
  layout : Layout t.lines.length (s.regs 4) (s.regs 6)
  storage : Storage (t.lines.map (physical a)) (s.regs 4) (s.regs 6)
  inputs : Inputs (t.lines.map (physical a)) s.memory
  linked : Linked (t.lines.map (physical a)) (load32 s.memory 0x2c120)
  count : (load32 s.memory 0x2c134).toNat=t.lines.length
  publishCount : Apart 0x2c134 (s.regs 5+82)
  publishInputs : ∀ e∈t.lines.map (physical a), Apart (e.address+46) (s.regs 5+82) ∧ Apart (e.address+50) (s.regs 5+82)
  countField : load32 s.memory (s.regs 5+78)=BitVec.ofNat 32 (t.sectors[i.val]).length
  keepCount : SafeWord (s.regs 5+78) (s.regs 4) (s.regs 6) t.lines.length
  keepPointer : SafeWord (s.regs 5+82) (s.regs 4) (s.regs 6) t.lines.length

/-- Original entry and complete scanning execution establish one sector's actual
count/pointer/ordered-array representation used by the sound traversal proofs. -/
theorem sector_rep (t : Topology) (a : Addresses)
    (addresses : OriginalGroupLines.SectorAddresses a t.sectors.length)
    (ranges : ∀ e∈t.lines, OriginalGroupLines.InRange e t.sectors.length)
    (grouped : t.Grouped) (i : Fin t.sectors.length) (s : X86Memory.State) (f : Option Flags)
    (setup : Setup t a i s) (nonempty : 0<t.lines.length) :
    ∃ out, X86Routine.run program [0x2e6af] (6+43*t.lines.length) ⟨s,f,0x2e661⟩=some out ∧
      out.pc=0x2e6af ∧ E1M1NoiseMap.Rep ⟨a.sector i.val,a.array i.val,(t.sectors[i.val]).map a.line⟩ out.core.memory := by
  have row := ordered_row t a addresses ranges grouped i
  have countField : load32 s.memory (s.regs 5+78)=BitVec.ofNat 32 (chosen (s.regs 5) (t.lines.map (physical a))).length := by
    rw [setup.sector,row,List.length_map]
    simpa [setup.sector] using setup.countField
  obtain ⟨out,run,done,rep⟩ := entry_rep (t.lines.map (physical a)) s f
    (by simpa using setup.layout) setup.storage setup.inputs setup.linked (by simpa using setup.count)
    setup.publishCount setup.publishInputs countField (by simpa using setup.keepCount)
    (by simpa using setup.keepPointer) (by simpa using nonempty)
  exact ⟨out,by simpa using run,done,by simpa only [setup.sector,setup.array,row] using rep⟩

end Doom.Proofs.E1M1GroupOutput

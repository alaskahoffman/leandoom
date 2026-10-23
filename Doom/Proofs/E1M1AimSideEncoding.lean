import Doom.Proofs.E1M1AimEncodedPortal
import Doom.Proofs.OriginalSideLoader
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimSideEncoding
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseImage (Realizes word half)
open E1M1AimEncodedPortal (Row sideBytes rawBytes)

def sectorAddress (base : Word) (index : Nat) : Word :=
  base+BitVec.ofNat 32 (index*86)

/-- Only the consumed bytes must survive between a loader endpoint and the
line-loader entry. This is a preservation obligation, not execution evidence
for the intervening startup code. -/
def Kept (p : E1M1NoiseImage.Patch) (before after : Memory) : Prop :=
  ∀ x∈p, after x.1=before x.1

/-- Entry contract for the already authenticated side-to-sector suffix.
Side-table indices and on-disk sector indices remain distinct. -/
structure Input (s : X86Memory.State) (side : BitVec 16) (index : Nat)
    (sideBase sectorBase : Word) : Prop where
  record : s.regs 2=sideBase+side.signExtend 32*18
  source : Realizes (half (s.regs 3+28) (BitVec.ofNat 16 index)) s.memory
  sectors : load32 s.memory 0x2c148=sectorBase
  safe : Apart 0x2c148 (s.regs 4)
  valid : index<32768

theorem word_of_load (m : Memory) (a v : Word) (value : load32 m a=v) :
    Realizes (word a v) m := by
  subst v
  intro x hx
  simp only [word,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl
  · simp only [load32]
    rw [BitVec.extractLsb'_append_eq_of_add_le (w:=16) (by decide)]
    exact BitVec.extractLsb'_append_eq_right.symm
  · simp only [load32]
    rw [BitVec.extractLsb'_append_eq_of_add_le (w:=16) (by decide)]
    exact BitVec.extractLsb'_append_eq_left.symm
  · simp only [load32]
    rw [BitVec.extractLsb'_append_eq_of_le (w:=16) (by decide)]
    exact BitVec.extractLsb'_append_eq_right.symm
  · simp only [load32]
    rw [BitVec.extractLsb'_append_eq_of_le (w:=16) (by decide)]
    exact BitVec.extractLsb'_append_eq_left.symm

theorem preserved (p : E1M1NoiseImage.Patch) (before after : Memory)
    (image : Realizes p before) (kept : Kept p before after) :
    Realizes p after := by
  intro x hx
  exact (kept x hx).trans (image x hx)

theorem publish_encoding (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run OriginalSideLoader.program [0x2e41c] 2 ⟨s,f,0x2e415⟩=
      some (OriginalSideLoader.published s f) ∧
    Realizes (word 0x2c118 (s.regs 0)) (OriginalSideLoader.published s f).core.memory := by
  refine ⟨OriginalSideLoader.publish_execution s f,word_of_load _ _ _ ?_⟩
  exact load_store _ _ _

theorem link_encoding (s : X86Memory.State) (f : Option Flags)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : Input s side index sideBase sectorBase) :
    X86Routine.run OriginalSideLoader.program [0x2e4d1] 11 ⟨s,f,0x2e4af⟩=
      some (OriginalSideLoader.linked s) ∧
    Realizes (word (E1M1NoiseGraph.sideAddress sideBase side) (sectorAddress sectorBase index))
      (OriginalSideLoader.linked s).core.memory := by
  refine ⟨OriginalSideLoader.link_execution s f,word_of_load _ _ _ ?_⟩
  have h := OriginalSideLoader.graph_pointer s side (BitVec.ofNat 16 index) sideBase sectorBase
    input.record (E1M1NoiseImage.read_half input.source) input.sectors input.safe
  have indexNat : (BitVec.ofNat 16 index).toNat=index := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := input.valid; omega)
  rw [OriginalSideLoader.nonnegative_offset _ (by rw [indexNat]; exact input.valid),indexNat] at h
  exact h

/-- Preservation across another pointer-emission suffix follows from its
actual two writes, including its temporary stack write. -/
theorem link_retains (s : X86Memory.State) (p : E1M1NoiseImage.Patch)
    (outside : ∀ x∈p, ∀ y∈OriginalSideLoader.linkPatch s, y.1≠x.1) :
    Kept p s.memory (OriginalSideLoader.linked s).core.memory := by
  intro x hx
  exact OriginalSideLoader.untouched s x.1 (outside x hx)

/-- Front and optional back pointers can come from different loader iterations.
No back execution is required for the sentinel; shared side addresses are
allowed. Preservation to the common entry memory is explicit. -/
theorem row_encoding (r : Row) (sideBase sectorBase : Word)
    (frontState backState : X86Memory.State) (ff bf : Option Flags) (m : Memory)
    (frontInput : Input frontState r.frontIndex r.frontSector sideBase sectorBase)
    (backInput : r.backIndex≠65535 → Input backState r.backIndex r.backSector sideBase sectorBase)
    (frontKept : Kept (word (E1M1NoiseGraph.sideAddress sideBase r.frontIndex)
      (sectorAddress sectorBase r.frontSector)) (OriginalSideLoader.linked frontState).core.memory m)
    (backKept : r.backIndex≠65535 → Kept (word (E1M1NoiseGraph.sideAddress sideBase r.backIndex)
      (sectorAddress sectorBase r.backSector)) (OriginalSideLoader.linked backState).core.memory m) :
    X86Routine.run OriginalSideLoader.program [0x2e4d1] 11 ⟨frontState,ff,0x2e4af⟩=
      some (OriginalSideLoader.linked frontState) ∧
    (r.backIndex≠65535 → X86Routine.run OriginalSideLoader.program [0x2e4d1] 11
      ⟨backState,bf,0x2e4af⟩=some (OriginalSideLoader.linked backState)) ∧
    Realizes (sideBytes r sideBase (sectorAddress sectorBase)) m := by
  have front := link_encoding frontState ff _ _ _ _ frontInput
  refine ⟨front.1,fun present => (link_encoding backState bf _ _ _ _ (backInput present)).1,?_⟩
  have first := preserved _ _ m front.2 frontKept
  intro x hx
  simp only [sideBytes,List.mem_append] at hx
  rcases hx with hx|hx
  · exact first x hx
  · by_cases missing : r.backIndex=65535
    · simp only [if_pos missing,List.not_mem_nil] at hx
    · simp only [if_neg missing] at hx
      exact preserved _ _ m (link_encoding backState bf _ _ _ _ (backInput missing)).2
        (backKept missing) x hx

theorem row_source (r : Row) (raw sideBase sectorBase : Word)
    (frontState backState : X86Memory.State) (ff bf : Option Flags) (m : Memory)
    (frontInput : Input frontState r.frontIndex r.frontSector sideBase sectorBase)
    (backInput : r.backIndex≠65535 → Input backState r.backIndex r.backSector sideBase sectorBase)
    (frontKept : Kept (word (E1M1NoiseGraph.sideAddress sideBase r.frontIndex)
      (sectorAddress sectorBase r.frontSector)) (OriginalSideLoader.linked frontState).core.memory m)
    (backKept : r.backIndex≠65535 → Kept (word (E1M1NoiseGraph.sideAddress sideBase r.backIndex)
      (sectorAddress sectorBase r.backSector)) (OriginalSideLoader.linked backState).core.memory m)
    (present : r.frontIndex≠65535) (global : load32 m 0x2c118=sideBase)
    (rawImage : Realizes (rawBytes r raw) m) :
    E1M1LineOutput.Source (E1M1AimEncodedPortal.sides r (sectorAddress sectorBase)) raw sideBase m := by
  exact E1M1AimEncodedPortal.side_source r raw sideBase _ m present global rawImage
    (row_encoding r sideBase sectorBase frontState backState ff bf m
      frontInput backInput frontKept backKept).2.2

/-- Replace Encoded.sides by actual suffix input contracts and byte preservation.
The other initial images, and reachability of these entries, remain obligations. -/
theorem initial_encoding (total : Nat) (rows : Fin total → Row)
    (raw vertexBase sideBase sectorBase : Word) (m : Memory)
    (frontState backState : Fin total → X86Memory.State)
    (frontInput : ∀ i, Input (frontState i) (rows i).frontIndex (rows i).frontSector sideBase sectorBase)
    (backInput : ∀ i, (rows i).backIndex≠65535 →
      Input (backState i) (rows i).backIndex (rows i).backSector sideBase sectorBase)
    (frontKept : ∀ i, Kept (word (E1M1NoiseGraph.sideAddress sideBase (rows i).frontIndex)
      (sectorAddress sectorBase (rows i).frontSector)) (OriginalSideLoader.linked (frontState i)).core.memory m)
    (backKept : ∀ i, (rows i).backIndex≠65535 →
      Kept (word (E1M1NoiseGraph.sideAddress sideBase (rows i).backIndex)
      (sectorAddress sectorBase (rows i).backSector)) (OriginalSideLoader.linked (backState i)).core.memory m)
    (globals : Realizes (word 0x2c138 vertexBase ++ word 0x2c118 sideBase) m)
    (rawImage : ∀ i, Realizes (rawBytes (rows i) (E1M1LineScan.cursor raw 14 i.val)) m)
    (vertices : ∀ i, Realizes (E1M1AimEncodedPortal.vertexBytes (rows i) vertexBase) m)
    (sectors : ∀ i, (rows i).backIndex≠65535 →
      Realizes (E1M1AimEncodedPortal.sectorBytes (rows i) (sectorAddress sectorBase)) m) :
    E1M1AimEncodedPortal.Encoded total rows raw vertexBase sideBase (sectorAddress sectorBase) m := by
  refine ⟨globals,rawImage,vertices,?_,sectors⟩
  intro i
  exact (row_encoding (rows i) sideBase sectorBase (frontState i) (backState i) none none m
    (frontInput i) (backInput i) (frontKept i) (backKept i)).2.2

end Doom.Proofs.E1M1AimSideEncoding

import Doom.Proofs.E1M1AimSideLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1AimPinnedSides
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimTextureCatalog E1M1AimPinnedCatalog E1M1AimSideLoop
open E1M1NoiseAllocation (Region)
-- Only numeric source-sector metadata. Reauthenticated against raw WAD bytes.
def sectorIndices : List (Fin 85) := [
  40,40,40,38,38,38,38,38,38,38,37,37,38,38,39,39,37,38,37,37,38,38,37,39,39,38,39,14,39,38,39,15,5,15,5,14,
  14,14,15,15,5,5,5,37,38,39,38,39,38,38,38,38,5,5,20,20,38,40,39,37,39,37,39,37,37,38,37,38,38,38,41,38,
  41,41,41,41,41,41,24,41,41,41,24,24,24,24,24,24,24,36,24,27,24,26,24,25,24,43,24,42,24,42,24,42,24,43,24,25,
  24,26,24,27,24,36,27,36,26,27,25,26,43,25,42,43,36,35,24,35,24,24,24,35,35,35,35,35,29,29,31,31,34,34,33,33,
  30,30,30,30,30,30,30,30,29,35,29,34,30,34,29,31,30,31,29,33,30,33,30,30,28,28,28,28,28,30,28,30,28,30,28,29,
  29,29,29,24,45,24,45,24,45,24,45,24,44,24,44,24,44,24,44,2,2,2,2,2,38,2,3,3,4,0,4,3,3,4,4,0,
  0,47,47,20,5,5,13,5,13,5,13,5,13,5,13,5,13,5,13,5,13,5,53,54,53,71,60,71,55,5,46,60,57,60,61,60,
  61,60,57,60,61,60,57,60,60,56,56,56,71,53,55,61,56,60,60,71,55,56,57,60,57,60,57,57,59,57,59,57,59,22,22,22,
  22,21,19,21,19,18,17,18,17,16,22,23,21,23,19,21,18,19,17,18,16,17,77,16,77,48,66,67,65,66,64,65,63,64,50,63,
  49,50,48,49,49,49,50,63,64,65,66,66,65,64,63,50,67,67,68,68,56,68,67,68,56,5,47,5,22,5,20,20,22,47,22,48,
  48,48,48,16,16,16,16,61,60,71,71,71,71,57,59,59,58,5,5,5,46,61,46,5,46,61,74,74,74,73,73,74,74,74,74,74,
  74,74,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,74,74,78,78,72,73,72,74,56,75,74,74,72,74,
  72,74,78,74,78,78,80,80,81,84,84,81,84,81,80,81,82,82,82,82,82,82,82,82,84,75,75,73,76,76,73,75,76,73,76,78,
  79,78,79,78,79,78,79,78,80,82,83,82,83,82,83,82,83,71,29,32,29,32,29,32,29,32,29,32,29,32,29,32,29,32,1,1,
  6,1,1,6,1,1,1,1,1,7,1,7,1,7,1,6,6,6,6,7,6,7,6,7,54,54,54,7,0,7,54,9,10,9,10,9,
  10,9,10,7,7,7,7,7,7,7,7,7,7,7,7,7,8,51,52,52,52,51,8,7,7,7,8,8,51,51,52,11,12,11,12,11,
  12,11,12,7,11,7,11,7,11,7,11,7,9,7,9,7,9,7,9,53,54,58,69,58,58,69,58,58,58,58,69,69,69,69,77,77,
  77,77,77,77,23,23,23,23,58,62,62,62,62,62,62,62,62,62,62,62,62,62,57,62,58,70,70,62,62,62,62,62,70,70,70,70]

def sectorIndex (row : Fin 648) : Nat := (sectorIndices[row.val]?.getD 0).val

def pinned (l : LayoutData) : LayoutData := { l with sectorIndex:=sectorIndex }

theorem dimensions : sectorIndices.length=648 := by decide +kernel

theorem sector_valid (row : Fin 648) : sectorIndex row<85 := by
  exact (sectorIndices[row.val]?.getD (0 : Fin 85)).isLt

/-- One common catalog and one raw source image. This does not assert that DOS
texture initialization or WAD loading has executed. Offset bytes are unrestricted
because they do not affect aiming sector pointers; the loop preserves them. -/
structure PinnedImage (l : LayoutData) (m : Memory) : Prop where
  table : load32 m 0x300e0=l.table
  textureCount : load32 m 0x300e4=125
  pointers : ∀ i<125, load32 m (l.table+4*BitVec.ofNat 32 i)=l.pointer i
  names : ∀ i<125, ∀ j<8, m (l.pointer i+BitVec.ofNat 32 j)=textureName i j
  rawNames : ∀ row k, ∀ j<8, m (query l row k+BitVec.ofNat 32 j)=queryName (fieldQuery row k) j
  rawSectors : ∀ row, E1M1NoiseImage.Realizes
    (E1M1NoiseImage.half (cursor l.raw 30 row.val+28) (BitVec.ofNat 16 (sectorIndex row))) m
  sectors : load32 m 0x2c148=l.sectors
  count : load32 m 0x2c11c=648
  published : load32 m 0x2c118=l.output

structure PinnedIncoming (l : LayoutData) (s : X86Memory.State) : Prop where
  registers : Registers (pinned l) 0 s
  image : PinnedImage l s.memory

theorem source_image (l : LayoutData) (m : Memory) (image : PinnedImage l m) : SourceImage (pinned l) m := by
  refine ⟨?_,?_,image.sectors,image.count,image.published⟩
  · intro row k
    exact ⟨image.table,image.textureCount,image.pointers,image.names,image.rawNames row k⟩
  · intro row
    exact E1M1NoiseImage.read_half (image.rawSectors row)

def layout (l : LayoutData) (storage : Storage (pinned l)) : Layout (pinned l) :=
  { storage with sectorValid:=fun row => Nat.lt_trans (sector_valid row) (by decide) }

/-- Reuses the complete loop. Source-sector Inputs and every reached catalog
image are derived; the only memory premise is PinnedIncoming at the first body. -/
theorem pinned_execution (l : LayoutData) (placement : Storage (pinned l)) (s : X86Memory.State)
    (f : Option Flags) (initial : PinnedIncoming l s) :
    (∃ k≤648*(3*(202*2147483647+30)+36),
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k
        ⟨s,f,0x2e46a⟩ (states s f 648)) ∧
    (states s f 648).pc=0x2e4dd ∧
    Outputs (pinned l) 648 (states s f 648).core.memory ∧
    (∀ p, Persistent (pinned l) p → load32 (states s f 648).core.memory p=load32 s.memory p) := by
  exact execution (pinned l) (layout l placement) s f
    ⟨initial.registers,source_image l s.memory initial.image⟩

/-- The independent CPU check's constructed placement, not a reachable DOS heap. -/
def constructed : LayoutData :=
  ⟨0x610000,0x620000,0x600f00,0x700000,0x601000,
    fun i => 0x602000+BitVec.ofNat 32 (16*i),sectorIndex⟩

/-- Nonvacuity of the regional storage hypotheses for the CPU fixture. -/
theorem constructed_storage : Nonempty (Storage (pinned constructed)) := by
  refine ⟨⟨⟨0x600ed4,0x600f04⟩,by decide +kernel,by decide +kernel,by decide +kernel,?_⟩⟩
  intro p hp
  have raw (i off : Nat) (hi : i<648) (ho : off<30) :
      (region (0x610000#32) 19443).Contains (cursor (0x610000#32) 30 i+BitVec.ofNat 32 off) := by
    have h := region_field (0x610000#32) 19443 (30*i+off) (by decide) (by omega)
    simpa [cursor,BitVec.ofNat_add,BitVec.add_assoc] using h
  rcases hp with rfl|rfl|rfl|⟨row,off,ho,rfl⟩|⟨row,k,hp⟩
  · exact ⟨⟨0x2c118,0x2c14c⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨⟨0x2c118,0x2c14c⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨⟨0x2c118,0x2c14c⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨region (0x610000#32) 19443,raw row.val off row.isLt ho,by decide +kernel,by decide +kernel⟩
  · rcases hp with rfl|rfl|⟨i,hi,rfl⟩|⟨i,hi,j,hj,rfl⟩|⟨j,hj,rfl⟩
    · exact ⟨⟨0x300e0,0x300e8⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
    · exact ⟨⟨0x300e0,0x300e8⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩
    · refine ⟨region (0x601000#32) 500,?_,by decide +kernel,by decide +kernel⟩
      change i<125 at hi
      simp [rowCatalog,catalog,pinned,constructed,region,Region.Contains,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat]
      omega
    · refine ⟨region (0x602000#32) 2000,?_,by decide +kernel,by decide +kernel⟩
      change i<125 at hi
      simp [rowCatalog,catalog,pinned,constructed,region,Region.Contains,BitVec.toNat_add,BitVec.toNat_ofNat]
      omega
    · refine ⟨region (0x610000#32) 19443,?_,by decide +kernel,by decide +kernel⟩
      have h := raw row.val (4+8*k.val+j) row.isLt (by have := k.isLt; omega)
      simpa [rowCatalog,catalog,query,pinned,constructed,BitVec.ofNat_add,BitVec.add_assoc] using h
end Doom.Proofs.E1M1AimPinnedSides

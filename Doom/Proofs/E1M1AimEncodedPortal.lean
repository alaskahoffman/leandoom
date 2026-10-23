import Doom.Proofs.E1M1AimRawPortal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimEncodedPortal
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1NoiseAllocation (Region)
open E1M1NoiseImage (Patch Realizes half word)
open E1M1LineScan (cursor states)

/-- Logical map data; sector addresses are supplied separately by relocation. -/
structure Row where
  geometry : E1M1LineSource.Record
  flags : BitVec 16
  frontIndex : BitVec 16
  backIndex : BitVec 16
  frontSector : Nat
  backSector : Nat
  ff : Word
  fc : Word
  bf : Word
  bc : Word

def sides (r : Row) (sector : Nat → Word) : E1M1LineOutput.Sides :=
  ⟨r.frontIndex,r.backIndex,sector r.frontSector,if r.backIndex=65535 then 0 else sector r.backSector⟩
def portal (r : Row) (sector : Nat → Word) :=
  E1M1AimInitialPortal.portal (sides r sector) r.ff r.fc r.bf r.bc

def rawBytes (r : Row) (raw : Word) : E1M1NoiseImage.Patch :=
  half raw r.geometry.first ++ half (raw+2) r.geometry.second ++ half (raw+4) r.flags ++
  half (raw+10) r.frontIndex ++ half (raw+12) r.backIndex

def vertexBytes (r : Row) (base : Word) : E1M1NoiseImage.Patch :=
  word (E1M1LineSource.address base r.geometry.first) r.geometry.x1 ++
  word (E1M1LineSource.address base r.geometry.first+4) r.geometry.y1 ++
  word (E1M1LineSource.address base r.geometry.second) r.geometry.x2 ++
  word (E1M1LineSource.address base r.geometry.second+4) r.geometry.y2

def sideBytes (r : Row) (base : Word) (sector : Nat → Word) : E1M1NoiseImage.Patch :=
  word (E1M1NoiseGraph.sideAddress base r.frontIndex) (sector r.frontSector) ++
  if r.backIndex=65535 then [] else
    word (E1M1NoiseGraph.sideAddress base r.backIndex) (sector r.backSector)

def sectorBytes (r : Row) (sector : Nat → Word) : E1M1NoiseImage.Patch :=
  word (sector r.frontSector) r.ff ++ word (sector r.frontSector+4) r.fc ++
  word (sector r.backSector) r.bf ++ word (sector r.backSector+4) r.bc

/-- Byte representation at line-loop entry, not an invented DOS initializer.
Only consumed bytes are constrained; unspecified memory stays arbitrary.
An absent back side requires no back-sector contents. -/
structure Encoded (total : Nat) (rows : Fin total → Row)
    (raw vertexBase sideBase : Word) (sector : Nat → Word) (m : Memory) : Prop where
  globals : Realizes (word 0x2c138 vertexBase ++ word 0x2c118 sideBase) m
  raw : ∀ i, Realizes (rawBytes (rows i) (cursor raw 14 i.val)) m
  vertices : ∀ i, Realizes (vertexBytes (rows i) vertexBase) m
  sides : ∀ i, Realizes (sideBytes (rows i) sideBase sector) m
  sectors : ∀ i, (rows i).backIndex≠65535 → Realizes (sectorBytes (rows i) sector) m

theorem geometry_source (r : Row) (raw base : Word) (m : Memory)
    (global : load32 m 0x2c138=base) (rawImage : Realizes (rawBytes r raw) m)
    (vertices : Realizes (vertexBytes r base) m) :
    E1M1LineSource.Source r.geometry raw base m := by
  refine ⟨global,?_,?_,?_,?_,?_,?_⟩
  · exact E1M1NoiseImage.read_half (fun x hx => rawImage x (by simp only [rawBytes,List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  · exact E1M1NoiseImage.read_half (fun x hx => rawImage x (by simp only [rawBytes,List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  · exact E1M1NoiseImage.read_word (fun x hx => vertices x (by simp only [vertexBytes,List.mem_append]; exact Or.inl (Or.inl (Or.inl hx))))
  · exact E1M1NoiseImage.read_word (fun x hx => vertices x (by simp only [vertexBytes,List.mem_append]; exact Or.inl (Or.inl (Or.inr hx))))
  · exact E1M1NoiseImage.read_word (fun x hx => vertices x (by simp only [vertexBytes,List.mem_append]; exact Or.inl (Or.inr hx)))
  · exact E1M1NoiseImage.read_word (fun x hx => vertices x (by simp only [vertexBytes,List.mem_append]; exact Or.inr hx))

theorem side_source (r : Row) (raw base : Word) (sector : Nat → Word) (m : Memory)
    (front : r.frontIndex≠65535) (global : load32 m 0x2c118=base)
    (rawImage : Realizes (rawBytes r raw) m) (sideImage : Realizes (sideBytes r base sector) m) :
    E1M1LineOutput.Source (sides r sector) raw base m := by
  refine ⟨global,?_,?_,?_,?_⟩
  · exact E1M1NoiseImage.read_half (fun x hx => rawImage x (by simp only [rawBytes,List.mem_append]; exact Or.inl (Or.inr hx)))
  · exact E1M1NoiseImage.read_half (fun x hx => rawImage x (by simp only [rawBytes,List.mem_append]; exact Or.inr hx))
  · simp only [sides,E1M1LineCache.target,if_neg front]
    exact E1M1NoiseImage.read_word (fun x hx => sideImage x (List.mem_append_left _ hx))
  · by_cases missing : r.backIndex=65535
    · simp [sides,E1M1LineCache.target,missing]
    · simp only [sides,E1M1LineCache.target,if_neg missing]
      exact E1M1NoiseImage.read_word (fun x hx => sideImage x (by simp only [sideBytes,if_neg missing]; exact List.mem_append_right _ hx))

theorem flag_byte (r : Row) (raw : Word) (m : Memory) (image : Realizes (rawBytes r raw) m) :
    m (raw+4)=r.flags.extractLsb' 0 8 := by
  exact image (raw+4,r.flags.extractLsb' 0 8) (by simp [rawBytes,half])

theorem sector_values (r : Row) (sector : Nat → Word) (m : Memory)
    (present : r.backIndex≠65535) (image : Realizes (sectorBytes r sector) m) :
    E1M1AimLoadedPortal.SectorValues m (portal r sector) := by
  simp only [E1M1AimLoadedPortal.SectorValues,portal,E1M1AimInitialPortal.portal,sides,if_neg present]
  refine ⟨?_,?_,?_,?_⟩
  · exact E1M1NoiseImage.read_word (fun x hx => image x (by simp only [sectorBytes,List.mem_append]; exact Or.inl (Or.inl (Or.inl hx))))
  · exact E1M1NoiseImage.read_word (fun x hx => image x (by simp only [sectorBytes,List.mem_append]; exact Or.inl (Or.inl (Or.inr hx))))
  · exact E1M1NoiseImage.read_word (fun x hx => image x (by simp only [sectorBytes,List.mem_append]; exact Or.inl (Or.inr hx)))
  · exact E1M1NoiseImage.read_word (fun x hx => image x (by simp only [sectorBytes,List.mem_append]; exact Or.inr hx))

theorem images (total : Nat) (rows : Fin total → Row) (raw vertexBase sideBase : Word)
    (sector : Nat → Word) (m : Memory)
    (encoded : Encoded total rows raw vertexBase sideBase sector m)
    (fronts : ∀ i, (rows i).frontIndex≠65535) :
    E1M1LineSource.Image (fun i => (rows i).geometry) raw vertexBase m ∧
    E1M1LineOutput.Image (fun i => sides (rows i) sector) raw sideBase m := by
  constructor
  · intro i
    exact geometry_source (rows i) _ _ m
      (E1M1NoiseImage.read_word (fun x hx => encoded.globals x (List.mem_append_left _ hx)))
      (encoded.raw i) (encoded.vertices i)
  · intro i
    exact side_source (rows i) _ _ sector m (fronts i)
      (E1M1NoiseImage.read_word (fun x hx => encoded.globals x (List.mem_append_right _ hx)))
      (encoded.raw i) (encoded.sides i)

/-- Decode the byte representation and apply the existing complete loader join.
Initial memory encoding and allocation are still premises, not startup results. -/
theorem execution (total : Nat) (rows : Fin total → Row) (sector : Nat → Word)
    (raw sideBase vertexBase base sp : Word) (stack : Region) (s : X86Memory.State)
    (f : Option Flags) (i : Fin total) (hit : Intercept)
    (loop : E1M1LineScan.Layout total base sp)
    (ready : E1M1LineScan.Ready total raw base sp 0 s)
    (verticesSafe : E1M1LineSource.ImageLayout (fun j => (rows j).geometry) raw vertexBase base sp)
    (good : ∀ j, E1M1LineSource.good (rows j).geometry=true)
    (sidesSafe : E1M1LineOutput.ImageLayout (fun j => sides (rows j) sector) raw sideBase base sp)
    (encoded : Encoded total rows raw vertexBase sideBase sector s.memory)
    (fronts : ∀ j, (rows j).frontIndex≠65535)
    (layout : E1M1AimLoadedScanRegions.Layout total base stack)
    (front : E1M1AimLoadedScanRegions.Sector total base (sector (rows i).frontSector) stack)
    (back : E1M1AimLoadedScanRegions.Sector total base (sector (rows i).backSector) stack)
    (reserve : E1M1AimLoadedScanRegions.Reserve stack sp)
    (present : (rows i).backIndex≠65535) (kind : hit.isLine=true)
    (flagSourceSafe : ∀ j, j<i.val → E1M1LineFrame.Protected
      (cursor raw 14 i.val+4) (cursor base 62 j) sp)
    (two : (rows i).flags.extractLsb' 0 8 &&& (4#8)≠0) :
    X86Routine.run E1M1LineIteration.program [0x2e3c1] (104*total) ⟨s,f,0x2e29a⟩=some (states s f total) ∧
    (states s f total).pc=0x2e3c1 ∧
    E1M1AimObjectCatalog.PortalValues (states s f total).core.memory hit (cursor base 62 i.val) (portal (rows i) sector) := by
  have initial := images total rows raw vertexBase sideBase sector s.memory encoded fronts
  apply E1M1AimRawPortal.execution_from_image total (fun j => sides (rows j) sector)
    (fun j => (rows j).geometry) raw sideBase vertexBase base sp stack s f i hit
    (rows i).ff (rows i).fc (rows i).bf (rows i).bc loop ready verticesSafe initial.1 good sidesSafe initial.2
    layout front (by simpa only [sides,if_neg present] using back) reserve present
    (sector_values (rows i) sector s.memory present (encoded.sectors i present)) kind flagSourceSafe
  rw [flag_byte (rows i) _ s.memory (encoded.raw i)]
  exact two
end Doom.Proofs.E1M1AimEncodedPortal

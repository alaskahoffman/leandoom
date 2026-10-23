import Doom.Proofs.E1M1PathMapLookup
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapLookup
namespace PathMapLookupFixture
-- An unaligned raw lump crosses address zero. Its cell keeps repeated line zero.
def base : Word := 0xfffffffb
def lines : Word := 0x700001
def words : Array Nat := #[0,0,36,23,5,0,0,474,65535]
def cell : Cell := ⟨5,[0,0,474]⟩
def memory : Memory :=
  [(base,0),(base+4,23*65536+36),(base+8,5),(base+12,474*65536),(base+16,65535),
   (0x2c100,base+8),(0x2c10c,base),(0x2c120,lines),
   (0x2c028,0x71000d),(0x710001,0x20000),(0x710005,1),(0x710009,lines+62)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def state : X86Memory.State :=
  ⟨fun r => if r=3 then 36 else if r=4 then 1 else 0,memory⟩

theorem image : WordImage state.memory base words := by
  intro i value h
  have bound : i<9 := by
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp h
    exact hi
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with h0|h0|h0|h0|h0|h0|h0|h0|h0
  all_goals
    subst i
    simp [words] at h
    subst value
    decide +kernel

theorem context : Context state base 0 0 36 := by constructor <;> decide +kernel
theorem valid : cell.Valid words := by decide +kernel

theorem joined :
    X86Routine.Prefix OriginalLineCell.program [] 8 ⟨state,none,0x2c541⟩ (OriginalLineCell.lookup state) ∧
    ScanWords (OriginalLineCell.lookup state).core lines cell :=
  lookup_to_scan state none base lines words cell 0 0 36 23 context (by decide)
    valid image (by decide) (by decide)

example : (OriginalLineCell.lookup state).core.regs 2=(5#32) := by decide +kernel
example : OriginalLineCell.itemWord (OriginalLineInvariant.atIndex (OriginalLineCell.lookup state).core 1)=0 := by decide +kernel
example : OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex (OriginalLineCell.lookup state).core 2)=lines+474*62 := by decide +kernel

def hit : Collision.Intercept := ⟨⟨0x20000⟩,true,1⟩
theorem collection : OriginalLineCollection.Tracks state 0x710001 (resolve lines) #[hit] 13 := by
  refine ⟨?_,by decide,by decide⟩
  intro i hi
  have eq : i=0 := by simpa using hi
  subst i
  change OriginalLineFinish.RecordAt state.memory 0x710001 hit (resolve lines hit)
  unfold OriginalLineFinish.RecordAt
  decide +kernel
example : OriginalLineCollection.Tracks (OriginalLineCell.lookup state).core 0x710001 (resolve lines) #[hit] 13 :=
  lookup_preserves_collection state 0x710001 (resolve lines) #[hit] 13 collection

#print axioms joined
end PathMapLookupFixture

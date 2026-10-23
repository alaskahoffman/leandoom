import Doom.Proofs.E1M1AimLineJoin
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1InterceptMark
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
attribute [local irreducible] load32 store32

/-- The exact set! update in the production ordered-hit visitor. -/
def consume (hits : Array Intercept) (j : Nat) : Array Intercept :=
  hits.set! j {hits[j]! with frac := ⟨2147483647⟩}

theorem size (hits : Array Intercept) (j : Nat) : (consume hits j).size=hits.size := by
  simp [consume]

theorem selected (hits : Array Intercept) (j : Nat) (inside : j<hits.size) :
    (consume hits j)[j]! = {hits[j]! with frac := ⟨2147483647⟩} := by
  exact Array.getElem!_set!_self hits j _ inside

theorem other (hits : Array Intercept) (j i : Nat) (different : j≠i) :
    (consume hits j)[i]! = hits[i]! := by
  exact Array.getElem!_set!_ne hits j i _ different

/-- Marking a fraction preserves tags, resolved pointers, and every other record.
The pointer resolver must ignore this selected hit's changed fraction. -/
theorem encoded (m : Memory) (hits : Array Intercept) (resolve : Intercept → Word)
    (j : Nat) (inside : j<hits.size) (bounded : hits.size≤128)
    (image : OriginalLineFinish.Encodes m 0x2ba20 resolve hits)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!) :
    OriginalLineFinish.Encodes (store32 m (address j) 0x7fffffff) 0x2ba20 resolve (consume hits j) := by
  intro i hi
  have old : i<hits.size := by simpa only [size] using hi
  have read := image i old
  have addr (k : Nat) : (0x2ba20 : Word)+BitVec.ofNat 32 (12*k)=address k := by
    simp [E1M1MinimumScan.address,BitVec.ofNat_add]
  simp only [OriginalLineFinish.RecordAt,addr] at read ⊢
  rw [←getElem!_pos (consume hits j) i hi,←getElem!_pos hits i old] at *
  by_cases eq : j=i
  · subst i
    rw [selected hits j inside]
    have apart (off : Word) (small : Apart off (0#32)) : Apart (address j+off) (address j) := by
      simpa only [BitVec.add_zero] using OriginalPathXStep.apart_translate (address j) off (0#32) small
    rw [load_store,load_store_apart _ _ _ _ (apart (4#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (apart (8#32) (by unfold Apart; decide)),stable]
    exact ⟨rfl,read.2⟩
  · rw [other hits j i eq]
    have keep (off : Word) (member : off∈[(0#32),4,8]) : Apart (address i+off) (address j) := by
      simpa only [addr,BitVec.add_zero] using OriginalLineCollection.slots_apart (0x2ba20 : Word)
        i j (by omega) (by omega) (Ne.symm eq) off (0#32) member (by simp)
    rw [load_store_apart _ _ _ _ (by simpa using keep (0#32) (by simp)),
      load_store_apart _ _ _ _ (keep (4#32) (by simp)),load_store_apart _ _ _ _ (keep (8#32) (by simp))]
    exact read
end Doom.Proofs.E1M1InterceptMark

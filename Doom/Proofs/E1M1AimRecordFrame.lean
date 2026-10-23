import Doom.Proofs.E1M1InterceptMark
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimRecordFrame
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
attribute [local irreducible] load32 store32

/-- Initial addresses separated from all callback prologue/helper/global writes. -/
def ReadSafe (s : X86Memory.State) (a : Word) : Prop :=
  E1M1AimWall.Safe (s.regs 4) a ∧ ∀ b∈E1M1AimReturnFrame.writes (s.regs 4), Apart a b

def RecordsSafe (s : X86Memory.State) (hits : Array Intercept) : Prop :=
  ∀ i<hits.size, ∀ off∈[(0#32),4,8], ReadSafe s (address i+off)

theorem frame (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc a : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc) (safe : ReadSafe s a) :
    load32 (E1M1AimWindow.result s).core.memory a=load32 s.memory a := by
  have mem := (OriginalAimWindow.result_fields (E1M1AimCeilingEntry.result s).core).2.2.1
  change load32 (OriginalAimWindow.result (E1M1AimCeilingEntry.result s).core).core.memory a=_
  rw [mem,E1M1AimReturnFrame.frame s hit line front back ff fc bf bc a h safe.2]
  exact E1M1AimWall.saved_frame s a safe.1

/-- The actual open-line callback leaves every intercept record intact. -/
theorem records (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (hits : Array Intercept) (resolve : Intercept → Word)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (safe : RecordsSafe s hits) :
    OriginalLineFinish.Encodes (E1M1AimWindow.result s).core.memory 0x2ba20 resolve hits := by
  intro i hi
  have addr : (0x2ba20 : Word)+BitVec.ofNat 32 (12*i)=address i := by simp [E1M1MinimumScan.address,BitVec.ofNat_add]
  have keep (off : Word) (member : off∈[(0#32),4,8]) := frame s hit line front back ff fc bf bc (address i+off) h (safe i hi off member)
  have old := image i hi
  simp only [OriginalLineFinish.RecordAt,addr] at old ⊢
  rw [show load32 (E1M1AimWindow.result s).core.memory (address i)=load32 s.memory (address i) by
      simpa using keep (0#32) (by simp),keep (4#32) (by simp),keep (8#32) (by simp)]
  exact old

/-- After the real parent mark, the complete buffer encodes the source's set!
update. No post-callback record image is assumed. -/
theorem resumed_records (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (hits : Array Intercept) (resolve : Intercept → Word) (j : Nat)
    (inside : j<hits.size) (bounded : hits.size≤128)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (safe : RecordsSafe s hits) (returnSafe : E1M1AimReturnFrame.Safe s)
    (pointer : s.regs 3=address j) (go : (E1M1AimWindow.result s).core.regs 0≠0)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!) :
    OriginalLineFinish.Encodes (E1M1AimResume.result s).core.memory 0x2ba20 resolve (E1M1InterceptMark.consume hits j) := by
  have ebx := (E1M1AimWindow.restored s hit line front back ff fc bf bc h returnSafe).2.2.2.2.2.2.2
  simp only [E1M1AimResume.result,OriginalInterceptGate.resumed,if_neg go,OriginalInterceptGate.marked,
    OriginalInterceptGate.restored,put,ebx,pointer]
  exact E1M1InterceptMark.encoded _ hits resolve j inside bounded (records s hit line front back ff fc bf bc h hits resolve image safe) stable

/-- Protected words also survive the parent's selected-fraction mark. -/
theorem resumed_frame (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc a : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (safe : ReadSafe s a) (returnSafe : E1M1AimReturnFrame.Safe s) (mark : Apart a (s.regs 3)) :
    load32 (E1M1AimResume.result s).core.memory a=load32 s.memory a := by
  have ebx := (E1M1AimWindow.restored s hit line front back ff fc bf bc h returnSafe).2.2.2.2.2.2.2
  unfold E1M1AimResume.result OriginalInterceptGate.resumed
  split
  · exact frame s hit line front back ff fc bf bc a h safe
  · change load32 (store32 (E1M1AimWindow.result s).core.memory ((E1M1AimWindow.result s).core.regs 3) 0x7fffffff) a=_
    rw [ebx,load_store_apart _ _ _ _ mark]
    exact frame s hit line front back ff fc bf bc a h safe

/-- The parent reloads its preserved cursor; the loop counter and maximum were
restored by the callback and survive both parent branches. -/
theorem registers (s : X86Memory.State) (hit : Intercept) (line front back ff fc bf bc : Word)
    (h : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)
    (returnSafe : E1M1AimReturnFrame.Safe s) (cursorSafe : ReadSafe s 0x2c028) :
    (E1M1AimResume.result s).core.regs 1=load32 s.memory 0x2c028 ∧
    (E1M1AimResume.result s).core.regs 4=s.regs 4+(4#32) ∧
    (E1M1AimResume.result s).core.regs 6=s.regs 6 ∧
    (E1M1AimResume.result s).core.regs 7=s.regs 7 := by
  have r := E1M1AimWindow.restored s hit line front back ff fc bf bc h returnSafe
  have cursor := frame s hit line front back ff fc bf bc 0x2c028 h cursorSafe
  unfold E1M1AimResume.result OriginalInterceptGate.resumed
  split <;> simp [OriginalInterceptGate.restored,OriginalInterceptGate.marked,put,write,r] <;> exact cursor
end Doom.Proofs.E1M1AimRecordFrame

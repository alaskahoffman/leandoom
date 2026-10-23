import Doom.Proofs.E1M1AimControllerEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimControllerFrame
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

def offsets : List Word := [4,8,12,16,20]
def slots (s : X86Memory.State) : List Word := offsets.map (s.regs 4+·)

/-- Relative to the first query entry: restore the four controller saves, the
unchanged EBP/EDI, and return through the original outer return word. -/
structure Restores (s : X86Memory.State) (out : X86Control.State) : Prop where
  stack : out.core.regs 4=s.regs 4+24
  pc : out.pc=(load32 s.memory (s.regs 4+20)).toNat
  bp : out.core.regs 5=s.regs 5
  di : out.core.regs 7=s.regs 7
  si : out.core.regs 6=load32 s.memory (s.regs 4+4)
  dx : out.core.regs 2=load32 s.memory (s.regs 4+8)
  cx : out.core.regs 1=load32 s.memory (s.regs 4+12)
  bx : out.core.regs 3=load32 s.memory (s.regs 4+16)

theorem finished (s t : X86Memory.State) (f : Option Flags)
    (stack : t.regs 4=s.regs 4+4) (bp : t.regs 5=s.regs 5) (di : t.regs 7=s.regs 7)
    (words : ∀ a∈slots s, load32 t.memory a=load32 s.memory a) :
    Restores s (OriginalBulletSlope.finished t f) := by
  have keep (off : Word) (member : off∈offsets) := words (s.regs 4+off) (List.mem_map.mpr ⟨off,member,rfl⟩)
  have k4 := keep 4 (by simp [offsets])
  have k8 := keep 8 (by simp [offsets])
  have k12 := keep 12 (by simp [offsets])
  have k16 := keep 16 (by simp [offsets])
  have k20 := keep 20 (by simp [offsets])
  constructor <;> simp [OriginalBulletSlope.finished,OriginalBulletSlope.pop,put,write,
    stack,bp,di,BitVec.add_assoc]
  all_goals first | exact k4 | exact k8 | exact k12 | exact k16 | exact congrArg BitVec.toNat k20

theorem accepted (second : Bool) (s : X86Memory.State) (out : X86Control.State)
    (stack : out.core.regs 4=s.regs 4+4)
    (bp : out.core.regs 5=s.regs 5) (di : out.core.regs 7=s.regs 7)
    (words : ∀ a∈slots s, load32 out.core.memory a=load32 s.memory a)
    (safe : ∀ a∈slots s, Apart a 0x2c0c0) :
    Restores s (E1M1BulletAim.accepted second out.core) := by
  apply finished
  · cases second <;> simpa [OriginalBulletSlope.decision,OriginalBulletSlope.stored,put,write] using stack
  · cases second <;> simpa [OriginalBulletSlope.decision,OriginalBulletSlope.stored,put,write] using bp
  · cases second <;> simpa [OriginalBulletSlope.decision,OriginalBulletSlope.stored,put,write] using di
  · intro a member
    exact (load_store_apart _ _ _ _ (safe a member)).trans (words a member)

theorem last (s : X86Memory.State) (out : X86Control.State)
    (stack : out.core.regs 4=s.regs 4+4)
    (bp : out.core.regs 5=s.regs 5) (di : out.core.regs 7=s.regs 7)
    (words : ∀ a∈slots s, load32 out.core.memory a=load32 s.memory a)
    (safe : ∀ a∈slots s, Apart a 0x2c0c0) :
    Restores s (E1M1BulletAim.lastReturn out.core out.flags) := by
  apply finished s (OriginalBulletSlope.stored out.core) out.flags stack bp di
  intro a member
  exact (load_store_apart _ _ _ _ (safe a member)).trans (words a member)

/-- Retries preserve EBP and EDI as well as the already-proved request fields. -/
theorem retry_registers (second : Bool) (s : X86Memory.State) :
    (E1M1BulletAim.nextQuery second s).core.regs 5=s.regs 5 ∧
    (E1M1BulletAim.nextQuery second s).core.regs 7=s.regs 7 := by
  cases second <;> simp [E1M1BulletAim.nextQuery,OriginalBulletSlope.retryState,OriginalBulletSlope.retry,
    OriginalBulletSlope.decision,OriginalBulletSlope.stored,X86Routine.pushWord,put,write]

/-- Rebase the suffix's stack slots to the original caller, using the actual
prologue's stored register values. No post-query saved-register premise. -/
theorem caller (s : X86Memory.State) (f : Option Flags) (out : X86Control.State)
    (restored : Restores (E1M1AimControllerEntry.entry s f).core out) :
    out.core.regs 4=s.regs 4+4 ∧ out.pc=(load32 s.memory (s.regs 4)).toNat ∧
    out.core.regs 5=s.regs 5 ∧ out.core.regs 7=s.regs 7 ∧
    out.core.regs 6=s.regs 6 ∧ out.core.regs 2=s.regs 2 ∧
    out.core.regs 1=s.regs 1 ∧ out.core.regs 3=s.regs 3 := by
  have sp : (E1M1AimControllerEntry.entry s f).core.regs 4=s.regs 4-20 := by
    simp [E1M1AimControllerEntry.entry,OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,
      X86Routine.pushWord,put,write,BitVec.sub_sub]
  obtain ⟨si,dx,cx,bx,pc⟩ := E1M1AimControllerEntry.saved s f
  rcases restored with ⟨stack,ret,bp,di,rsi,rdx,rcx,rbx⟩
  rw [sp,BitVec.sub_add_cancel] at ret
  simp only [sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] at stack rsi rdx rcx rbx
  have bp0 : (E1M1AimControllerEntry.entry s f).core.regs 5=s.regs 5 := by
    simp [E1M1AimControllerEntry.entry,OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,put,write]
  have di0 : (E1M1AimControllerEntry.entry s f).core.regs 7=s.regs 7 := by
    simp [E1M1AimControllerEntry.entry,OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,put,write]
  simp only [BitVec.sub_eq_add_neg] at si dx cx bx
  exact ⟨stack,ret.trans (congrArg BitVec.toNat pc),bp.trans bp0,di.trans di0,
    rsi.trans si,rdx.trans dx,rcx.trans cx,rbx.trans bx⟩
end Doom.Proofs.E1M1AimControllerFrame

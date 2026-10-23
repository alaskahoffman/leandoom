import Doom.Proofs.E1M1AimPortalSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimOpeningFrame
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32

def caller (s : X86Memory.State) := OriginalAimGuard.lineCore (OriginalAimGuard.prepared s)
def helper (s : X86Memory.State) := OriginalAimOpening.called (caller s)
def result (s : X86Memory.State) := E1M1AimOpening.result (caller s)
def pushes (sp : Word) : List Word :=
  [sp-(4#32),sp-(8#32),sp-(12#32),sp-(16#32),sp-(20#32),sp-(24#32),sp-(28#32)]
def writes (sp : Word) : List Word := pushes sp ++
  [sp-(32#32),sp-(36#32),sp-(40#32),sp-(44#32)] ++ E1M1NoiseLineProgress.openingGlobals

def MapSafe (s : X86Memory.State) (line front back : Word) : Prop :=
  E1M1NoiseLedger.Protect (E1M1OpeningHeights.reads line front back) (writes (s.regs 4))

structure Image (memory : Memory) (line front back ff fc bf bc : Word) : Prop where
  side : load16 memory (line+(24#32))≠0xffff
  frontPtr : load32 memory (line+(46#32))=front
  backPtr : load32 memory (line+(50#32))=back
  frontFloor : load32 memory front=ff
  frontCeiling : load32 memory (front+(4#32))=fc
  backFloor : load32 memory back=bf
  backCeiling : load32 memory (back+(4#32))=bc

theorem stack (s : X86Memory.State) :
    (caller s).regs 4=s.regs 4-(24#32) ∧ (helper s).regs 4=s.regs 4-(28#32) := by
  simp [caller,helper,OriginalAimOpening.called,OriginalAimOpening.argument,
    OriginalAimGuard.lineCore,OriginalAimGuard.prepared,OriginalAimGuard.saved,
    OriginalAimGuard.save6,OriginalAimGuard.save5,OriginalAimGuard.save4,OriginalAimGuard.save3,
    OriginalAimGuard.save2,OriginalAimGuard.save1,X86Routine.pushWord,put,write,BitVec.sub_sub]

theorem line_argument (s : X86Memory.State) (hit : Collision.Intercept) (pointer : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (safe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+8)) :
    (caller s).regs 1=pointer ∧ (helper s).regs 0=pointer := by
  have ptr : OriginalAimGuard.line (OriginalAimGuard.prepared s)=pointer := by
    change load32 (OriginalAimGuard.saved s).memory (s.regs 0+8)=pointer
    rw [E1M1AimWall.saved_frame s _ safe]; exact record.2.2
  simp [caller,helper,OriginalAimOpening.called,OriginalAimOpening.argument,
    OriginalAimGuard.lineCore,X86Routine.pushWord,put,write,ptr]

/-- The callback prologue plus CALL changes only seven stack words. -/
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈pushes (s.regs 4), Apart a b) :
    load32 (helper s).memory a=load32 s.memory a := by
  have old : E1M1AimWall.Safe (s.regs 4) a := by
    intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> exact safe _ (by simp [pushes])
  change load32 (store32 (caller s).memory ((caller s).regs 4-(4#32)) (0x2b786#32)) a=_
  rw [(stack s).1]
  have addr : s.regs 4-(24#32)-(4#32)=s.regs 4-(28#32) := by simp [BitVec.sub_sub]
  rw [addr,load_store_apart _ _ _ _ (safe _ (by simp [pushes]))]
  exact E1M1AimWall.saved_frame s a old

theorem half_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈pushes (s.regs 4), Apart a b) :
    load16 (helper s).memory a=load16 s.memory a := by
  have h := congrArg (fun w : Word => w.extractLsb' 0 16) (frame s a safe)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using h

/-- Derive the helper-entry sector representation from callback-entry memory. -/
theorem transport (s : X86Memory.State) (line front back ff fc bf bc : Word)
    (safe : MapSafe s line front back) (image : Image s.memory line front back ff fc bf bc) :
    Image (helper s).memory line front back ff fc bf bc := by
  have keep (a : Word) (ha : a∈E1M1OpeningHeights.reads line front back) :=
    frame s a (fun b hb => safe a ha b (by simp only [writes,List.mem_append]; exact Or.inl (Or.inl hb)))
  have half := half_frame s (line+(24#32)) (fun b hb => safe _ (by simp [E1M1OpeningHeights.reads]) b
    (by simp only [writes,List.mem_append]; exact Or.inl (Or.inl hb)))
  constructor
  · rw [half]; exact image.side
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact image.frontPtr
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact image.backPtr
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact image.frontFloor
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact image.frontCeiling
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact image.backFloor
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact image.backCeiling

theorem helper_safe (s : X86Memory.State) (line front back : Word)
    (arg : (helper s).regs 0=line) (safe : MapSafe s line front back) :
    E1M1OpeningHeights.Safe (helper s) front back := by
  intro a ha b hb
  apply safe a (by simpa only [arg] using ha) b
  simp [E1M1OpeningHeights.saves,(stack s).2,BitVec.sub_sub] at hb
  simp [writes,pushes]
  rcases hb with (rfl|rfl|rfl|rfl)|hb <;> simp_all

/-- All height inputs are now at callback entry, not supplied at the later CALL. -/
theorem decision (s : X86Memory.State) (hit : Collision.Intercept)
    (line front back ff fc bf bc : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit line)
    (pointerSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+8))
    (mapSafe : MapSafe s line front back) (image : Image s.memory line front back ff fc bf bc) :
    (result s).pc=if (if bc.toInt≤fc.toInt then bc else fc).toInt ≤
      (if ff.toInt≤bf.toInt then bf else ff).toInt then 0x2b8d2 else 0x2b797 := by
  have args := line_argument s hit line record pointerSafe
  have img := transport s line front back ff fc bf bc mapSafe image
  apply E1M1AimOpening.height_decision (caller s) front back ff fc bf bc
    (helper_safe s line front back args.2 mapSafe)
  · simpa only [helper,args.1] using img.side
  · simpa only [helper,args.1] using img.frontPtr
  · simpa only [helper,args.1] using img.backPtr
  · exact img.frontFloor
  · exact img.frontCeiling
  · exact img.backFloor
  · exact img.backCeiling

/-- Reusable frame for the full opening helper, independent of its caller. -/
theorem opening_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈E1M1OpeningHeights.saves s ++ E1M1NoiseLineProgress.openingGlobals, Apart a b) :
    load32 (E1M1NoiseOpening.result s).core.memory a=load32 s.memory a := by
  have keep (m : Memory) (v : Word) (b : Word)
      (hb : b∈E1M1OpeningHeights.saves s ++ E1M1NoiseLineProgress.openingGlobals) :=
    load_store_apart m b a v (safe b hb)
  simp only [E1M1NoiseOpening.result]
  split <;> simp only [NoiseOpening.closed,NoiseOpening.entry,NoiseOpening.prepared,NoiseOpening.saved,
    NoiseOpening.returned,NoiseOpening.range,NoiseOpening.floor,NoiseOpening.floorInputs,
    NoiseOpening.ceiling,NoiseOpening.ceilingInputs,PspriteLoop.popped,X86Routine.pushWord,put,write]
  all_goals
    simp only [ite_true,ite_false,BitVec.sub_sub]
    repeat rw [keep _ _ _ (by simp [E1M1OpeningHeights.saves,E1M1NoiseLineProgress.openingGlobals])]

/-- Protect a caller word through both prologues, the real CALL and all helper
global writes. This includes the intercept fraction and attack range. -/
theorem output_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈writes (s.regs 4), Apart a b) :
    load32 (result s).core.memory a=load32 s.memory a := by
  change load32 (E1M1NoiseOpening.result (helper s)).core.memory a=_
  rw [opening_frame]
  · exact frame s a (fun b hb => safe b (by simp only [writes,List.mem_append]; exact Or.inl (Or.inl hb)))
  · intro b hb
    apply safe b
    simp [E1M1OpeningHeights.saves,(stack s).2,BitVec.sub_sub] at hb
    simp [writes,pushes]
    rcases hb with (rfl|rfl|rfl|rfl)|hb <;> simp_all

theorem output_regs (s : X86Memory.State) (safe : E1M1AimOpening.CallerSafe s) :
    (result s).core.regs 2=s.regs 0 ∧ (result s).core.regs 4=s.regs 4-(24#32) := by
  have localSafe : E1M1AimOpening.Safe (caller s) := by
    simpa [E1M1AimOpening.Safe,E1M1AimOpening.CallerSafe,(stack s).1,BitVec.sub_sub] using safe
  have h := E1M1AimOpening.helper_return (caller s) localSafe
  change (E1M1AimOpening.result (caller s)).core.regs 2=_ ∧
    (E1M1AimOpening.result (caller s)).core.regs 4=_
  simp only [E1M1AimOpening.result,OriginalAimOpening.gate,OriginalAimOpening.loaded,put,write]
  simp only [show (2 : Reg)≠0 by decide,show (4 : Reg)≠0 by decide,ite_false,h.2.2.1,h.2.2.2,(stack s).1]
  constructor
  · simp [caller,OriginalAimGuard.lineCore,OriginalAimGuard.prepared,put,write]
  · trivial
end Doom.Proofs.E1M1AimOpeningFrame

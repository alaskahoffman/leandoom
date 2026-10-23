import Doom.Proofs.E1M1PathGridSetup
import Doom.Proofs.OriginalLineBounds
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PathCell
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1PathGridSetup.program pc with
  | some op => some op
  | none => match OriginalPathCell.program pc with
    | some op => some op
    | none => OriginalLineBounds.program pc

theorem contains_prior (pc : Nat) (h : E1M1PathGridSetup.program pc≠none) :
    program pc=E1M1PathGridSetup.program pc := by
  unfold program
  cases hp : E1M1PathGridSetup.program pc <;> simp_all

theorem contains_cell (pc : Nat) (h : OriginalPathCell.program pc≠none) :
    program pc=OriginalPathCell.program pc := by
  have range : 0x2ca7f≤pc ∧ pc<0x2cab5 := by
    by_cases r : 0x2ca7f≤pc ∧ pc<0x2cab5
    · exact r
    · simp [OriginalPathCell.program,OriginalPathCell.bytesProgram,r] at h
  have all : ∀ i : Fin 54, program (0x2ca7f+i.val)=OriginalPathCell.program (0x2ca7f+i.val) := by decide
  have eq : 0x2ca7f+(pc-0x2ca7f)=pc := by omega
  simpa only [eq] using all ⟨pc-0x2ca7f,by omega⟩

theorem contains_bounds (pc : Nat) (h : OriginalLineBounds.program pc≠none) :
    program pc=OriginalLineBounds.program pc := by
  by_cases r : 0x2c520≤pc ∧ pc<0x2c541
  · have all : ∀ i : Fin 33, program (0x2c520+i.val)=OriginalLineBounds.program (0x2c520+i.val) := by decide
    have eq : 0x2c520+(pc-0x2c520)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c520,by omega⟩
  · have tail : 0x2c587≤pc ∧ pc<0x2c591 := by
      by_cases t : 0x2c587≤pc ∧ pc<0x2c591
      · exact t
      · simp [OriginalLineBounds.program,OriginalLineBounds.bytesProgram,r,t] at h
    have all : ∀ i : Fin 10, program (0x2c587+i.val)=OriginalLineBounds.program (0x2c587+i.val) := by decide
    have eq : 0x2c587+(pc-0x2c587)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c587,by omega⟩

private theorem flags_apart (sp off : Word) (h : off∈[0,4,28,32,36,40,44,-4,-8,-12,-16]) :
    Apart (sp+64) (sp+off) := by
  apply OriginalPathXStep.apart_translate
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem x_flags (s : X86Memory.State) :
    load32 (OriginalPathXStep.result s).core.memory ((OriginalPathXStep.result s).core.regs 4+64)=
    load32 s.memory (s.regs 4+64) := by
  rw [PathXStepFrame.stack]
  apply PathXStepFrame.frame
  intro b hb
  simp only [PathXStepFrame.writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa using flags_apart (s.regs 4) 0 (by simp)
  all_goals simpa [BitVec.sub_eq_add_neg] using flags_apart (s.regs 4) _ (by simp)

theorem first_flags (s : X86Memory.State) :
    load32 (OriginalPathIntercept.result s).core.memory ((OriginalPathIntercept.result s).core.regs 4+64)=
    load32 s.memory (s.regs 4+64) := by
  change load32 (OriginalPathIntercept.result s).core.memory (s.regs 4+64)=_
  apply OriginalPathIntercept.frame
  intro off h
  apply flags_apart
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl <;> simp

theorem y_flags (s : X86Memory.State) :
    load32 (OriginalPathYStep.result s).core.memory ((OriginalPathYStep.result s).core.regs 4+64)=
    load32 s.memory (s.regs 4+64) := by
  rw [(OriginalPathYStep.preserved s).1]
  apply OriginalPathYStep.frame
  intro b hb
  simp only [OriginalPathYStep.writes,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl
  all_goals simpa [BitVec.sub_eq_add_neg] using flags_apart (s.regs 4) _ (by simp)

theorem second_flags (s : X86Memory.State) :
    load32 (OriginalPathSecondIntercept.result s).core.memory ((OriginalPathSecondIntercept.result s).core.regs 4+64)=
    load32 s.memory (s.regs 4+64) := by
  change load32 (OriginalPathSecondIntercept.result s).core.memory (s.regs 4+64)=_
  exact OriginalPathSecondIntercept.frame s _ (flags_apart _ 36 (by simp))

theorem flags_from_init (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : OriginalPathInit.Inputs s ox oy sx sy ex ey) :
    let t := E1M1PathGridSetup.after (OriginalPathIntercept.result
      (OriginalPathXStep.result (OriginalPathInit.result s).core).core).core
    load32 t.core.memory (t.core.regs 4+64)=load32 s.memory (s.regs 4+4) := by
  dsimp only [E1M1PathGridSetup.after]
  rw [second_flags,y_flags,first_flags,x_flags,(OriginalPathInit.ready s ox oy sx sy ex ey h).stack]
  change load32 (OriginalPathInit.result s).core.memory (s.regs 4-(60#32)+(64#32))=_
  rw [OriginalPathInit.stack_64,OriginalPathInit.memory]
  exact OriginalPathInit.frame15 s _ (h.safeReads _ (by simp [OriginalPathInit.reads]))

theorem low_byte (m : Memory) (a : Word) : (load32 m a).extractLsb' 0 8=m a := by
  simp only [load32]
  bv_decide

/-- The real aim caller supplies BOTH traversal bits; setup preserves them. -/
theorem first_flags_from_caller (gun : Fire.Gun) (s : X86Memory.State)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core) :
    OriginalPathCell.enabled true (E1M1PathGridSetup.firstGrid gun s).core=true := by
  have frame := flags_from_init _ ox oy sx sy ex ey geometry
  have supplied := congrArg (fun v => v.2.1) (OriginalAimSetup.call_frame _ layout)
  have word : load32 (E1M1PathGridSetup.firstGrid gun s).core.memory
      ((E1M1PathGridSetup.firstGrid gun s).core.regs 4+64)=(3#32) := frame.trans supplied
  have byte := congrArg (fun v : Word => v.extractLsb' 0 8) word
  rw [low_byte] at byte
  change (E1M1PathGridSetup.firstGrid gun s).core.memory
    ((E1M1PathGridSetup.firstGrid gun s).core.regs 4+(64#32))=(3#8) at byte
  simp [OriginalPathCell.enabled,OriginalPathCell.optionBits,OriginalPathCell.mask,byte]

def firstCall (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalPathCell.called true (E1M1PathGridSetup.firstGrid gun s).core
    (OriginalPathCell.gateFlags true (E1M1PathGridSetup.firstGrid gun s).core)
def firstBounds (gun : Fire.Gun) (s : X86Memory.State) := OriginalLineBounds.result (firstCall gun s).core

/-- One continuous firing prefix, through the actual first line-iterator bounds.
No visitor body or callback is replaced with an assumed result. -/
theorem first_bounds_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout) :
    ∃ n, n≤360 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstBounds gun s) ∧
    (firstCall gun s).core.regs 0=(Collision.pathStart ox oy sx sy ex ey).startBlockX.toBitVec ∧
    (firstCall gun s).core.regs 2=(Collision.pathStart ox oy sx sy ex ey).startBlockY.toBitVec := by
  obtain ⟨n,hn,a,ready⟩ := E1M1PathGridSetup.first_grid_correspondence gun s f c h
    ox oy sx sy ex ey geometry xout yout okX okY
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := OriginalPathCell.enter_execution true (E1M1PathGridSetup.firstGrid gun s).core
    (E1M1PathGridSetup.firstGrid gun s).flags
  have flag := first_flags_from_caller gun s ox oy sx sy ex ey geometry layout
  simp only [OriginalPathCell.enter,flag,↓reduceIte] at b
  have b := X86CodeMemory.lift_success (b.transfer program [] contains_cell (by simp)) FloorCaller.cm
  change X86CodeMemory.Prefix _ _ _ m ⟨_,_,0x2ca7f⟩ (firstCall gun s) at b
  rw [OriginalPathXStep.at_pc _ _ ready.pc] at b
  obtain ⟨k,hk,d⟩ := OriginalLineBounds.execution (firstCall gun s).core (firstCall gun s).flags
  have d := X86CodeMemory.lift_success (d.transfer program [] contains_bounds (by simp)) FloorCaller.cm
  have pc : (firstCall gun s).pc=0x2c520 := rfl
  rw [OriginalPathXStep.at_pc _ _ pc] at d
  have args := OriginalPathCell.call_inputs true (E1M1PathGridSetup.firstGrid gun s).core
    (OriginalPathCell.gateFlags true (E1M1PathGridSetup.firstGrid gun s).core)
  exact ⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans a b) d,
    args.1.trans ready.mapX,args.2.1.trans ready.mapY⟩
end Doom.Proofs.E1M1PathCell

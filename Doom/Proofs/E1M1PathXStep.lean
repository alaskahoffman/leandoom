import Doom.Proofs.E1M1PathInit
import Doom.Proofs.OriginalPathXStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1PathXStep
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match E1M1PathInit.program pc with
  | some op => some op
  | none => OriginalPathXStep.program pc

theorem contains_prior (pc : Nat) (h : E1M1PathInit.program pc≠none) :
    program pc=E1M1PathInit.program pc := by
  unfold program
  cases hp : E1M1PathInit.program pc <;> simp_all

theorem contains_step (pc : Nat) (h : OriginalPathXStep.program pc≠none) :
    program pc=OriginalPathXStep.program pc := by
  have absent : E1M1PathInit.program pc=none := by
    by_cases x : 0x2c96c≤pc ∧ pc<0x2c9d3
    · have all : ∀ i : Fin 103, E1M1PathInit.program (0x2c96c+i.val)=none := by decide
      have eq : 0x2c96c+(pc-0x2c96c)=pc := by omega
      simpa only [eq] using all ⟨pc-0x2c96c,by omega⟩
    · by_cases a : 0x418d8≤pc ∧ pc<0x418df
      · have all : ∀ i : Fin 7, E1M1PathInit.program (0x418d8+i.val)=none := by decide
        have eq : 0x418d8+(pc-0x418d8)=pc := by omega
        simpa only [eq] using all ⟨pc-0x418d8,by omega⟩
      · have d : 0x1d180≤pc ∧ pc<0x1d1c1 := by
          by_cases d : 0x1d180≤pc ∧ pc<0x1d1c1
          · exact d
          · simp [OriginalPathXStep.program,x,a,OriginalDivMemory.program,OriginalDivMemory.bytesProgram,d] at h
        have all : ∀ i : Fin 65, E1M1PathInit.program (0x1d180+i.val)=none := by decide
        have eq : 0x1d180+(pc-0x1d180)=pc := by omega
        simpa only [eq] using all ⟨pc-0x1d180,by omega⟩
  simp [program,absent]

def firstXStep (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalPathXStep.result (E1M1PathInit.firstPath gun s).core

theorem first_xstep_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (safe : OriginalPathXStep.Safe (E1M1PathInit.firstPath gun s).core) :
    ∃ n, n≤268 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstXStep gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1PathInit.first_path_execution gun s f c h
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := OriginalPathXStep.execution (E1M1PathInit.firstPath gun s).core
    (E1M1PathInit.firstPath gun s).flags safe
  have b := (X86CodeMemory.lift_success b FloorCaller.cm).transfer program [] contains_step (by simp)
  have pc : (E1M1PathInit.firstPath gun s).pc=0x2c96c := rfl
  rw [OriginalPathXStep.at_pc _ _ pc] at b
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- All coordinate and stack-local inputs are supplied by the prior initialization
proof. There is no new representation assumption at the X-step seam. -/
theorem inputs_from_init (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (h : OriginalPathInit.Inputs s ox oy sx sy ex ey) :
    OriginalPathXStep.Inputs (OriginalPathInit.result s).core (Collision.pathStart ox oy sx sy ex ey) := by
  have ready := OriginalPathInit.ready s ox oy sx sy ex ey h
  constructor
  · exact congrArg (fun v => v.1) ready.relative
  · exact congrArg (fun v => v.2.2.1) ready.relative
  · obtain ⟨_,_,_,_,hy⟩ := OriginalPathInit.loaded_origins s ox oy sx sy ex ey h
    obtain ⟨_,ny⟩ := OriginalPathInit.nudges s ox oy sx sy ex ey h
    simp only [OriginalPathInit.result,OriginalPathInit.c60,OriginalPathInit.c59,OriginalPathInit.c58,OriginalPathInit.c57,OriginalPathInit.c56,OriginalPathInit.c55,OriginalPathInit.c54,OriginalPathInit.c53,OriginalPathInit.c52,OriginalPathInit.c51,OriginalPathInit.c50,OriginalPathInit.c49,OriginalPathInit.c48,OriginalPathInit.c47,OriginalPathInit.c46,OriginalPathInit.c45,OriginalPathInit.c44,OriginalPathInit.c43,OriginalPathInit.c42,OriginalPathInit.c41,OriginalPathInit.c40,OriginalPathInit.c39,OriginalPathInit.c38,OriginalPathInit.c37,OriginalPathInit.c36,OriginalPathInit.c35,OriginalPathInit.c34,OriginalPathInit.c33,OriginalPathInit.c32,OriginalPathInit.c31,OriginalPathInit.c30,OriginalPathInit.c29,OriginalPathInit.c28,OriginalPathInit.c27,OriginalPathInit.c26,OriginalPathInit.c25,OriginalPathInit.c24,OriginalPathInit.c23,OriginalPathInit.c22,OriginalPathInit.c21,OriginalPathInit.c20,OriginalPathInit.c19,OriginalPathInit.c18,OriginalPathInit.c17,OriginalPathInit.c16,OriginalPathInit.c15,OriginalPathInit.c14,OriginalPathInit.c13,OriginalPathInit.c12,OriginalPathInit.c11,OriginalPathInit.c10,OriginalPathInit.c9,OriginalPathInit.c8,OriginalPathInit.c7,OriginalPathInit.c6,OriginalPathInit.c5,OriginalPathInit.c4,OriginalPathInit.c3,OriginalPathInit.c2,OriginalPathInit.c1,put,write]
    simp only [hy,ny,h.endY]
    rfl
  · rw [ready.stack]
    have addr : s.regs 4-60+12=s.regs 4-48 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact congrArg (fun v => v.1) ready.blocks
  · rw [ready.stack]
    have addr : s.regs 4-60+20=s.regs 4-40 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact congrArg (fun v => v.2.2.1) ready.blocks
  · rw [ready.stack]
    have addr : s.regs 4-60+8=s.regs 4-52 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact ready.fraction

/-- Live arithmetic success discharges the machine division condition, and the
preceding initialization supplies the inputs. Returns one continuous execution. -/
theorem first_xstep_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (out : Int32 × Fixed × Fixed) (ok : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok out) :
    ∃ n, n≤268 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstXStep gun s) ∧
    OriginalPathXStep.observe (E1M1PathInit.firstPath gun s).core (firstXStep gun s)=
      OriginalPathXStep.liveObserve out := by
  have inputs := inputs_from_init _ ox oy sx sy ex ey geometry
  have matched :=  OriginalPathXStep.live (E1M1PathInit.firstPath gun s).core _ out inputs ok
  obtain ⟨n,hn,path⟩ := first_xstep_execution gun s f c h matched.1
  exact ⟨n,hn,path,matched.2⟩
end Doom.Proofs.E1M1PathXStep

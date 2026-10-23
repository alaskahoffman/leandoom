import Doom.Proofs.E1M1DischargeSetters
import Doom.Proofs.OriginalBulletSlope
import Doom.Proofs.BulletAim
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1BulletAim
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2d7c0 ≤ pc ∧ pc < 0x2d823 then OriginalBulletSlope.program pc
  else E1M1DischargeSetters.program pc

theorem contains_prior (pc : Nat) (h : E1M1DischargeSetters.program pc≠none) :
    program pc=E1M1DischargeSetters.program pc := by
  by_cases inside : 0x2d7c0 ≤ pc ∧ pc < 0x2d823
  · have checked : ∀ i : Fin 99, E1M1DischargeSetters.program (0x2d7c0+i.val)=none := by decide
    have eq : 0x2d7c0+(pc-0x2d7c0)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2d7c0,by omega⟩))
  · simp [program,inside]
theorem contains_slope (pc : Nat) (h : OriginalBulletSlope.program pc≠none) :
    program pc=OriginalBulletSlope.program pc := by
  by_cases inside : 0x2d7c0 ≤ pc ∧ pc < 0x2d823
  · simp [program,inside]
  · exact False.elim (h (by simp [OriginalBulletSlope.program,OriginalBulletSlope.bytesProgram,inside]))

def firstQuery (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalBulletSlope.firstCall (E1M1DischargeSetters.aimCall gun s).core (E1M1DischargeSetters.aimCall gun s).flags

/-- Extends the previous post-sound execution through P_BulletSlope's real
prologue and CALL into P_AimLineAttack. The traversal is not assumed executed. -/
theorem first_query_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c) :
    ∃ n, n≤127 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstQuery gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1DischargeSetters.aim_execution gun s f c h.actor h.related h.poseSafe h.tables h.tableSafe h.separated
  have a := a.transfer program [] contains_prior (by simp)
  have b := X86CodeMemory.lift_success (OriginalBulletSlope.first_execution
    (E1M1DischargeSetters.aimCall gun s).core (E1M1DischargeSetters.aimCall gun s).flags) FloorCaller.cm
  have eq : E1M1DischargeSetters.aimCall gun s =
      ⟨(E1M1DischargeSetters.aimCall gun s).core,(E1M1DischargeSetters.aimCall gun s).flags,0x2d7c0⟩ := rfl
  rw [←eq] at b
  exact ⟨n+9,by omega,E1M1PspriteStep.prefix_trans a (b.transfer program [] contains_slope (by simp))⟩

/-- The first actual geometry CALL uses the related actor angle and 1024 units. -/
theorem first_query_request (gun : Fire.Gun) (s : X86Memory.State) (angle : Angle)
    (value : load32 (E1M1DischargeSetters.aimCall gun s).core.memory
      ((E1M1DischargeSetters.aimCall gun s).core.regs 0+32)=angle.raw.toBitVec)
    (safe : ∀ b, b ∈ OriginalBulletSlope.saveWrites (E1M1DischargeSetters.aimCall gun s).core →
      Apart ((E1M1DischargeSetters.aimCall gun s).core.regs 0+32) b) :
    (firstQuery gun s).core.regs 0=(E1M1DischargeSetters.aimCall gun s).core.regs 0 ∧
    (firstQuery gun s).core.regs 2=angle.raw.toBitVec ∧
    (firstQuery gun s).core.regs 3=(Fixed.ofInt 1024).raw.toBitVec := by
  have args := OriginalBulletSlope.first_arguments (E1M1DischargeSetters.aimCall gun s).core (E1M1DischargeSetters.aimCall gun s).flags
  rw [OriginalBulletSlope.initial_angle _ angle value safe] at args
  exact args

def accepted (second : Bool) (s : X86Memory.State) :=
  OriginalBulletSlope.finished (OriginalBulletSlope.decision second s).core (OriginalBulletSlope.decision second s).flags
def nextQuery (second : Bool) (s : X86Memory.State) :=
  OriginalBulletSlope.retryState second (OriginalBulletSlope.decision second s).core (OriginalBulletSlope.decision second s).flags

theorem accepted_execution (second : Bool) (s : X86Memory.State) (f : Option Flags)
    (hit : OriginalBulletSlope.target s≠0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 9
      ⟨s,f,if second then 0x2d7f8 else 0x2d7d5⟩ (accepted second s) := by
  have a := (X86CodeMemory.lift_success (OriginalBulletSlope.decision_execution second s f) FloorCaller.cm).transfer program [] contains_slope (by simp)
  have b := (X86CodeMemory.lift_success (OriginalBulletSlope.finish_execution
    (OriginalBulletSlope.decision second s).core (OriginalBulletSlope.decision second s).flags) FloorCaller.cm).transfer program [] contains_slope (by simp)
  have eq : OriginalBulletSlope.decision second s =
      ⟨(OriginalBulletSlope.decision second s).core,(OriginalBulletSlope.decision second s).flags,0x2d81e⟩ := by
    have hit' : OriginalBulletSlope.target s≠(0#32) := hit
    simp [OriginalBulletSlope.decision,hit']
  rw [←eq] at b
  exact E1M1PspriteStep.prefix_trans a b

theorem next_query_execution (second : Bool) (s : X86Memory.State) (f : Option Flags)
    (miss : OriginalBulletSlope.target s=0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] (4+(if second then 4 else 5))
      ⟨s,f,if second then 0x2d7f8 else 0x2d7d5⟩ (nextQuery second s) := by
  have a := (X86CodeMemory.lift_success (OriginalBulletSlope.decision_execution second s f) FloorCaller.cm).transfer program [] contains_slope (by simp)
  have b := (X86CodeMemory.lift_success (OriginalBulletSlope.retry_execution second
    (OriginalBulletSlope.decision second s).core (OriginalBulletSlope.decision second s).flags) FloorCaller.cm).transfer program [] contains_slope (by simp)
  have eq : OriginalBulletSlope.decision second s =
      ⟨(OriginalBulletSlope.decision second s).core,(OriginalBulletSlope.decision second s).flags,
        if second then 0x2d807 else 0x2d7e4⟩ := by simp [OriginalBulletSlope.decision,miss]
  rw [←eq] at b
  exact E1M1PspriteStep.prefix_trans a b

def lastReturn (s : X86Memory.State) (f : Option Flags) := OriginalBulletSlope.finished (OriginalBulletSlope.stored s) f

theorem last_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤6 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2d819⟩ (lastReturn s f) := by
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (OriginalBulletSlope.last_store_execution s f)
  have a := (X86CodeMemory.lift_success (a.transfer OriginalBulletSlope.program [] (by intros; rfl) (by simp)) FloorCaller.cm).transfer program [] contains_slope (by simp)
  have b := (X86CodeMemory.lift_success (OriginalBulletSlope.finish_execution (OriginalBulletSlope.stored s) f) FloorCaller.cm).transfer program [] contains_slope (by simp)
  exact ⟨n+5,by omega,E1M1PspriteStep.prefix_trans a b⟩

theorem accepted_slope (second : Bool) (s : X86Memory.State) :
    load32 (accepted second s).core.memory 0x2c0c0=s.regs 0 := by
  unfold accepted
  rw [OriginalBulletSlope.finished_slope]
  exact OriginalBulletSlope.stored_slope s
theorem last_slope (s : X86Memory.State) (f : Option Flags) :
    load32 (lastReturn s f).core.memory 0x2c0c0=s.regs 0 := by
  unfold lastReturn
  rw [OriginalBulletSlope.finished_slope]
  exact OriginalBulletSlope.stored_slope s

/-- Modular 32-bit arithmetic for the two retries, including wraparound.
The second retry subtracts 1/32 turn from the first retry's angle. -/
theorem retry_angles (angle : UInt32) :
    (angle.toBitVec+0x04000000)+0xf8000000=(angle+0xfc000000).toBitVec := by
  change (angle.toBitVec+0x04000000)+0xf8000000=angle.toBitVec+0xfc000000
  simp only [BitVec.add_assoc]; rfl

/-- The geometry obligation includes target presence, even for a zero slope. -/
structure ProbeResult (s : X86Memory.State) (r : Collision.AimResult) : Prop where
  slope : s.regs 0=r.slope.raw.toBitVec
  presence : (OriginalBulletSlope.target s≠0) ↔ r.target.isSome=true

theorem center_correspondence (scene : Collision.Scene) (shooter : Nat) (angle : Angle)
    (r : Collision.AimResult) (s : X86Memory.State)
    (query : BulletAim.query scene shooter angle 0=.ok r)
    (related : ProbeResult s r) (hit : OriginalBulletSlope.target s≠0) :
    ∃ selected, scene.bulletAim shooter angle=.ok selected ∧
      load32 (accepted false s).core.memory 0x2c0c0=selected.slope.raw.toBitVec := by
  refine ⟨BulletAim.selection angle 0 r,BulletAim.live_center scene shooter angle r query (related.presence.mp hit),?_⟩
  rw [accepted_slope]; exact related.slope

theorem right_correspondence (scene : Collision.Scene) (shooter : Nat) (angle : Angle)
    (a b : Collision.AimResult) (s : X86Memory.State)
    (p0 : BulletAim.query scene shooter angle 0=.ok a)
    (p1 : BulletAim.query scene shooter angle 0x04000000=.ok b)
    (no0 : a.target.isSome=false) (related : ProbeResult s b) (hit : OriginalBulletSlope.target s≠0) :
    ∃ selected, scene.bulletAim shooter angle=.ok selected ∧
      load32 (accepted true s).core.memory 0x2c0c0=selected.slope.raw.toBitVec := by
  refine ⟨BulletAim.selection angle 0x04000000 b,BulletAim.live_right scene shooter angle a b p0 p1 no0 (related.presence.mp hit),?_⟩
  rw [accepted_slope]; exact related.slope

theorem last_correspondence (scene : Collision.Scene) (shooter : Nat) (angle : Angle)
    (a b c : Collision.AimResult) (s : X86Memory.State) (f : Option Flags)
    (p0 : BulletAim.query scene shooter angle 0=.ok a)
    (p1 : BulletAim.query scene shooter angle 0x04000000=.ok b)
    (p2 : BulletAim.query scene shooter angle 0xfc000000=.ok c)
    (no0 : a.target.isSome=false) (no1 : b.target.isSome=false)
    (related : ProbeResult s c) (zero : c.target.isSome=false → c.slope=⟨0⟩) :
    ∃ selected, scene.bulletAim shooter angle=.ok selected ∧
      load32 (lastReturn s f).core.memory 0x2c0c0=selected.slope.raw.toBitVec := by
  by_cases hit : c.target.isSome=true
  · refine ⟨BulletAim.selection angle 0xfc000000 c,BulletAim.live_left scene shooter angle a b c p0 p1 p2 no0 no1 hit,?_⟩
    rw [last_slope]; exact related.slope
  · have no2 : c.target.isSome=false := by cases h : c.target.isSome <;> simp_all
    refine ⟨{facing:=angle},BulletAim.live_miss scene shooter angle a b c p0 p1 p2 no0 no1 no2,?_⟩
    rw [last_slope,related.slope,zero no2]
end Doom.Proofs.E1M1BulletAim

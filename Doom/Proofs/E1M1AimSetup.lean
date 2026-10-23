import Doom.Proofs.E1M1AimQuery
import Doom.Proofs.OriginalAimSetup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1AimSetup
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2bba0 ≤ pc ∧ pc < 0x2bbff then OriginalAimSetup.program pc
  else E1M1AimQuery.program pc

theorem contains_prior (pc : Nat) (h : E1M1AimQuery.program pc≠none) :
    program pc=E1M1AimQuery.program pc := by
  by_cases inside : 0x2bba0 ≤ pc ∧ pc < 0x2bbff
  · have checked : ∀ i : Fin 95, E1M1AimQuery.program (0x2bba0+i.val)=none := by decide
    have eq : 0x2bba0+(pc-0x2bba0)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2bba0,by omega⟩))
  · simp [program,inside]

theorem contains_setup (pc : Nat) (h : OriginalAimSetup.program pc≠none) :
    program pc=OriginalAimSetup.program pc := by
  by_cases inside : 0x2bba0 ≤ pc ∧ pc < 0x2bbff
  · simp [program,inside]
  · exact False.elim (h (by simp [OriginalAimSetup.program,OriginalAimSetup.bytesProgram,inside]))

def firstTraversal (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalAimSetup.traversal (E1M1AimQuery.firstRay gun s).core

/-- The real firing prefix now reaches P_PathTraverse, including its CALL.
No map traversal or callback result is assumed executed. -/
theorem first_traversal_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c) :
    ∃ n, n≤163 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstTraversal gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1AimQuery.first_ray_execution gun s f c h
  have a := a.transfer program [] contains_prior (by simp)
  have b := (X86CodeMemory.lift_success (OriginalAimSetup.execution
    (E1M1AimQuery.firstRay gun s).core (E1M1AimQuery.firstRay gun s).flags)
    FloorCaller.cm).transfer program [] contains_setup (by simp)
  have eq : E1M1AimQuery.firstRay gun s=
      ⟨(E1M1AimQuery.firstRay gun s).core,(E1M1AimQuery.firstRay gun s).flags,0x2bba0⟩ := rfl
  rw [←eq] at b
  exact ⟨n+25,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- All 36 instructions from query entry through the traversal CALL, reusable
for center, right and left probes and arbitrary input memory. -/
theorem query_setup_execution (s : X86Memory.State) (f : Option Flags) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 36 ⟨s,f,0x2bb80⟩
      (OriginalAimSetup.traversal (OriginalAimQuery.ray s).core) := by
  have a := (X86CodeMemory.lift_success (OriginalAimQuery.ray_execution s f)
    FloorCaller.cm).transfer E1M1AimQuery.program [] E1M1AimQuery.contains_query (by simp)
  have a := a.transfer program [] contains_prior (by simp)
  have b := (X86CodeMemory.lift_success (OriginalAimSetup.execution (OriginalAimQuery.ray s).core none)
    FloorCaller.cm).transfer program [] contains_setup (by simp)
  exact E1M1PspriteStep.prefix_trans a b

/-- Displacement correspondence is supplied by the proved ray arithmetic;
only shooter encoding and separation at the setup boundary remain premises. -/
theorem inputs_from_ray (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance : Fixed) (ray : OriginalAimQuery.RayInputs s angle distance)
    (x : load32 (OriginalAimQuery.ray s).core.memory (s.regs 0+12)=thing.x.raw.toBitVec)
    (y : load32 (OriginalAimQuery.ray s).core.memory (s.regs 0+16)=thing.y.raw.toBitVec)
    (z : load32 (OriginalAimQuery.ray s).core.memory (s.regs 0+20)=thing.z.raw.toBitVec)
    (height : load32 (OriginalAimQuery.ray s).core.memory (s.regs 0+68)=thing.height.raw.toBitVec)
    (reads : ∀ a, a ∈ OriginalAimSetup.actorReads (OriginalAimQuery.ray s).core →
      ∀ b, b ∈ (OriginalAimSetup.writes (OriginalAimQuery.ray s).core).toList → Apart a b)
    (separated : OriginalAimSetup.Separated (OriginalAimQuery.ray s).core) :
    OriginalAimSetup.Inputs (OriginalAimQuery.ray s).core thing angle distance := by
  have actor : (OriginalAimQuery.ray s).core.regs 0=s.regs 0 := by
    simp [OriginalAimQuery.ray,OriginalAimQuery.saved,X86Routine.pushWord,put,write]
  have range : (OriginalAimQuery.ray s).core.regs 3=distance.raw.toBitVec := by
    simpa [OriginalAimQuery.ray,OriginalAimQuery.saved,X86Routine.pushWord,put,write] using ray.rangeReg
  exact ⟨by simpa only [actor] using x,by simpa only [actor] using y,
    by simpa only [actor] using z,by simpa only [actor] using height,range,
    OriginalAimQuery.live_endpoint s thing angle distance ray,reads,separated⟩

/-- The query return proofs remain available in the same combined program. -/
theorem final_miss_execution (s : X86Memory.State) (f : Option Flags)
    (resume : (load32 s.memory (s.regs 4+16)).toNat=0x2d819)
    (miss : OriginalAimQuery.target s=0) :
    ∃ n, n≤14 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2bbff⟩
      (E1M1BulletAim.lastReturn (OriginalAimQuery.returned s).core (OriginalAimQuery.returned s).flags) ∧
    load32 (E1M1BulletAim.lastReturn (OriginalAimQuery.returned s).core
      (OriginalAimQuery.returned s).flags).core.memory 0x2c0c0=0 := by
  obtain ⟨n,hn,path⟩ := E1M1AimQuery.return_to_last s f resume
  exact ⟨n,hn,path.transfer program [] contains_prior (by simp),E1M1AimQuery.last_miss_zero s miss⟩
/-- Connect execution to the live Lean geometry inputs at the very same boundary. -/
theorem first_traversal_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (thing : Collision.SolidThing) (angle : Angle)
    (geometry : OriginalAimSetup.Inputs (E1M1AimQuery.firstRay gun s).core thing angle (Fixed.ofInt 1024)) :
    ∃ n, n≤163 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstTraversal gun s) ∧
    OriginalAimSetup.Ready (E1M1AimQuery.firstRay gun s).core (firstTraversal gun s)
      thing angle (Fixed.ofInt 1024) := by
  obtain ⟨n,hn,path⟩ := first_traversal_execution gun s f c h
  exact ⟨n,hn,path,OriginalAimSetup.ready _ thing angle _ geometry⟩
end Doom.Proofs.E1M1AimSetup

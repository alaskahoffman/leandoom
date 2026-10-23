import Doom.Proofs.E1M1BulletAim
import Doom.Proofs.OriginalAimQuery
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1AimQuery
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x2bb80 ≤ pc ∧ pc < 0x2bba0) ∨ (0x2bbff ≤ pc ∧ pc < 0x2bc19) then
    OriginalAimQuery.program pc else E1M1BulletAim.program pc

theorem contains_prior (pc : Nat) (h : E1M1BulletAim.program pc≠none) :
    program pc=E1M1BulletAim.program pc := by
  by_cases a : 0x2bb80 ≤ pc ∧ pc < 0x2bba0
  · have checked : ∀ i : Fin 32, E1M1BulletAim.program (0x2bb80+i.val)=none := by decide
    have eq : 0x2bb80+(pc-0x2bb80)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2bb80,by omega⟩))
  · by_cases b : 0x2bbff ≤ pc ∧ pc < 0x2bc19
    · have checked : ∀ i : Fin 26, E1M1BulletAim.program (0x2bbff+i.val)=none := by decide
      have eq : 0x2bbff+(pc-0x2bbff)=pc := by omega
      exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2bbff,by omega⟩))
    · simp [program,a,b]

theorem contains_query (pc : Nat) (h : OriginalAimQuery.program pc≠none) :
    program pc=OriginalAimQuery.program pc := by
  by_cases a : 0x2bb80 ≤ pc ∧ pc < 0x2bba0
  · simp [program,a]
  · by_cases b : 0x2bbff ≤ pc ∧ pc < 0x2bc19
    · simp [program,b]
    · exact False.elim (h (by simp [OriginalAimQuery.program,OriginalAimQuery.bytesProgram,a,b]))

def firstRay (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalAimQuery.ray (E1M1BulletAim.firstQuery gun s).core

/-- The actual firing prefix now executes through both ray multiplications.
It stops before the geometry callback is pushed, not after a geometry query. -/
theorem first_ray_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c) :
    ∃ n, n≤138 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstRay gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1BulletAim.first_query_execution gun s f c h
  have a := a.transfer program [] contains_prior (by simp)
  have b := (X86CodeMemory.lift_success (OriginalAimQuery.ray_execution
    (E1M1BulletAim.firstQuery gun s).core (E1M1BulletAim.firstQuery gun s).flags)
    FloorCaller.cm).transfer program [] contains_query (by simp)
  have eq : E1M1BulletAim.firstQuery gun s =
      ⟨(E1M1BulletAim.firstQuery gun s).core,(E1M1BulletAim.firstQuery gun s).flags,0x2bb80⟩ := rfl
  rw [←eq] at b
  exact ⟨n+11,by omega,E1M1PspriteStep.prefix_trans a b⟩

theorem first_ray_endpoint (gun : Fire.Gun) (s : X86Memory.State)
    (thing : Collision.SolidThing) (angle : Angle)
    (h : OriginalAimQuery.RayInputs (E1M1BulletAim.firstQuery gun s).core angle (Fixed.ofInt 1024)) :
    (thing.x.raw.toBitVec+(firstRay gun s).core.regs 1,
     thing.y.raw.toBitVec+(firstRay gun s).core.regs 6)=
    ((thing.attackEndpoint angle (Fixed.ofInt 1024)).1.raw.toBitVec,
     (thing.attackEndpoint angle (Fixed.ofInt 1024)).2.raw.toBitVec) :=
  OriginalAimQuery.live_endpoint _ thing angle _ h

/-- The traversal still owes its result and preserved return frame. Given its
actual return address, the epilogue connects to the already verified controller. -/
theorem return_to_accept (second : Bool) (s : X86Memory.State) (f : Option Flags)
    (resume : (load32 s.memory (s.regs 4+16)).toNat=if second then 0x2d7f8 else 0x2d7d5)
    (hit : OriginalAimQuery.target s≠0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 17 ⟨s,f,0x2bbff⟩
      (E1M1BulletAim.accepted second (OriginalAimQuery.returned s).core) := by
  have a := (X86CodeMemory.lift_success (OriginalAimQuery.return_execution s f)
    FloorCaller.cm).transfer program [] contains_query (by simp)
  have hit' : OriginalBulletSlope.target (OriginalAimQuery.returned s).core≠0 := hit
  have b := (E1M1BulletAim.accepted_execution second (OriginalAimQuery.returned s).core
    (OriginalAimQuery.returned s).flags hit').transfer program [] contains_prior (by simp)
  have pc : (OriginalAimQuery.returned s).pc=if second then 0x2d7f8 else 0x2d7d5 := by
    simpa [OriginalAimQuery.returned,OriginalAimQuery.pop,put,write,BitVec.add_assoc] using resume
  have eq : OriginalAimQuery.returned s=
    ⟨(OriginalAimQuery.returned s).core,(OriginalAimQuery.returned s).flags,
      if second then 0x2d7f8 else 0x2d7d5⟩ := by rw [←pc]
  rw [←eq] at b
  exact E1M1PspriteStep.prefix_trans a b

theorem return_to_retry (second : Bool) (s : X86Memory.State) (f : Option Flags)
    (resume : (load32 s.memory (s.regs 4+16)).toNat=if second then 0x2d7f8 else 0x2d7d5)
    (miss : OriginalAimQuery.target s=0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] (8+(4+(if second then 4 else 5)))
      ⟨s,f,0x2bbff⟩ (E1M1BulletAim.nextQuery second (OriginalAimQuery.returned s).core) := by
  have a := (X86CodeMemory.lift_success (OriginalAimQuery.return_execution s f)
    FloorCaller.cm).transfer program [] contains_query (by simp)
  have miss' : OriginalBulletSlope.target (OriginalAimQuery.returned s).core=0 := miss
  have b := (E1M1BulletAim.next_query_execution second (OriginalAimQuery.returned s).core
    (OriginalAimQuery.returned s).flags miss').transfer program [] contains_prior (by simp)
  have pc : (OriginalAimQuery.returned s).pc=if second then 0x2d7f8 else 0x2d7d5 := by
    simpa [OriginalAimQuery.returned,OriginalAimQuery.pop,put,write,BitVec.add_assoc] using resume
  have eq : OriginalAimQuery.returned s=
    ⟨(OriginalAimQuery.returned s).core,(OriginalAimQuery.returned s).flags,
      if second then 0x2d7f8 else 0x2d7d5⟩ := by rw [←pc]
  rw [←eq] at b
  exact E1M1PspriteStep.prefix_trans a b

theorem return_to_last (s : X86Memory.State) (f : Option Flags)
    (resume : (load32 s.memory (s.regs 4+16)).toNat=0x2d819) :
    ∃ n, n≤14 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2bbff⟩
      (E1M1BulletAim.lastReturn (OriginalAimQuery.returned s).core (OriginalAimQuery.returned s).flags) := by
  have a := (X86CodeMemory.lift_success (OriginalAimQuery.return_execution s f)
    FloorCaller.cm).transfer program [] contains_query (by simp)
  obtain ⟨n,hn,b⟩ := E1M1BulletAim.last_execution (OriginalAimQuery.returned s).core (OriginalAimQuery.returned s).flags
  have b := b.transfer program [] contains_prior (by simp)
  have pc : (OriginalAimQuery.returned s).pc=0x2d819 := by
    simpa [OriginalAimQuery.returned,OriginalAimQuery.pop,put,write,BitVec.add_assoc] using resume
  have eq : OriginalAimQuery.returned s=
    ⟨(OriginalAimQuery.returned s).core,(OriginalAimQuery.returned s).flags,0x2d819⟩ := by rw [←pc]
  rw [←eq] at b
  exact ⟨8+n,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- Closes the DOS side of the final-query zero-on-miss obligation. -/
theorem last_miss_zero (s : X86Memory.State) (miss : OriginalAimQuery.target s=0) :
    load32 (E1M1BulletAim.lastReturn (OriginalAimQuery.returned s).core
      (OriginalAimQuery.returned s).flags).core.memory 0x2c0c0=0 := by
  rw [E1M1BulletAim.last_slope,OriginalAimQuery.return_miss s miss]

/-- An accepted zero-slope target remains a hit; this uses the target predicate. -/
theorem accepted_result (second : Bool) (s : X86Memory.State) (hit : OriginalAimQuery.target s≠0) :
    load32 (E1M1BulletAim.accepted second (OriginalAimQuery.returned s).core).core.memory 0x2c0c0=
      load32 s.memory 0x2b9b4 := by
  rw [E1M1BulletAim.accepted_slope,OriginalAimQuery.return_hit s hit]
end Doom.Proofs.E1M1AimQuery

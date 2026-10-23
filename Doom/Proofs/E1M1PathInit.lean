import Doom.Proofs.E1M1AimSetup
import Doom.Proofs.OriginalPathInit
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1PathInit
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2c8a0 ≤ pc ∧ pc < 0x2c96c then OriginalPathInit.program pc
  else E1M1AimSetup.program pc

theorem contains_prior (pc : Nat) (h : E1M1AimSetup.program pc≠none) :
    program pc=E1M1AimSetup.program pc := by
  by_cases inside : 0x2c8a0 ≤ pc ∧ pc < 0x2c96c
  · have checked : ∀ i : Fin 204, E1M1AimSetup.program (0x2c8a0+i.val)=none := by decide
    have eq : 0x2c8a0+(pc-0x2c8a0)=pc := by omega
    exact False.elim (h (by simpa only [eq] using checked ⟨pc-0x2c8a0,by omega⟩))
  · simp [program,inside]

theorem contains_init (pc : Nat) (h : OriginalPathInit.program pc≠none) :
    program pc=OriginalPathInit.program pc := by
  by_cases inside : 0x2c8a0 ≤ pc ∧ pc < 0x2c96c
  · simp [program,inside]
  · exact False.elim (h (by simp [OriginalPathInit.program,OriginalPathInit.bytesProgram,inside]))

def firstPath (gun : Fire.Gun) (s : X86Memory.State) :=
  OriginalPathInit.result (E1M1AimSetup.firstTraversal gun s).core

/-- The real firing prefix reaches the first block stepping comparison. -/
theorem first_path_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c) :
    ∃ n, n≤223 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstPath gun s) := by
  obtain ⟨n,hn,a⟩ := E1M1AimSetup.first_traversal_execution gun s f c h
  have a := a.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := OriginalPathInit.execution (E1M1AimSetup.firstTraversal gun s).core
    (E1M1AimSetup.firstTraversal gun s).flags
  have b := (X86CodeMemory.lift_success b FloorCaller.cm).transfer program [] contains_init (by simp)
  have eq : E1M1AimSetup.firstTraversal gun s=
      ⟨(E1M1AimSetup.firstTraversal gun s).core,(E1M1AimSetup.firstTraversal gun s).flags,0x2c8a0⟩ := rfl
  rw [←eq] at b
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- Reusable for any of the three aim probes, with arbitrary initial byte memory. -/
theorem query_path_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤96 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2bb80⟩
      (OriginalPathInit.result (OriginalAimSetup.traversal (OriginalAimQuery.ray s).core).core) := by
  have a := (E1M1AimSetup.query_setup_execution s f).transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,b⟩ := OriginalPathInit.execution (OriginalAimSetup.traversal (OriginalAimQuery.ray s).core).core none
  have b := (X86CodeMemory.lift_success b FloorCaller.cm).transfer program [] contains_init (by simp)
  exact ⟨36+m,by omega,E1M1PspriteStep.prefix_trans a b⟩

/-- Execution and the live production geometry meet at the same machine state.
Map/stack encoding is still an explicit boundary obligation. -/
theorem first_path_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey) :
    ∃ n, n≤223 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstPath gun s) ∧
    OriginalPathInit.Ready (E1M1AimSetup.firstTraversal gun s).core (firstPath gun s)
      (Collision.pathStart ox oy sx sy ex ey) := by
  obtain ⟨n,hn,path⟩ := first_path_execution gun s f c h
  exact ⟨n,hn,path,OriginalPathInit.ready _ ox oy sx sy ex ey geometry⟩

/-- Reuse the preceding query's proved coordinates; only map/stack layout is new. -/
theorem inputs_from_setup (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance ox oy : Fixed) (h : OriginalAimSetup.Inputs s thing angle distance)
    (originX : load32 (OriginalAimSetup.traversal s).core.memory 0x2c104=ox.raw.toBitVec)
    (originY : load32 (OriginalAimSetup.traversal s).core.memory 0x2c108=oy.raw.toBitVec)
    (safeReads : ∀ a, a ∈ OriginalPathInit.reads (OriginalAimSetup.traversal s).core →
      ∀ b, b ∈ (OriginalPathInit.writes (OriginalAimSetup.traversal s).core).toList → Apart a b)
    (separated : OriginalPathInit.Separated (OriginalAimSetup.traversal s).core) :
    OriginalPathInit.Inputs (OriginalAimSetup.traversal s).core ox oy thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 := by
  have coords := OriginalAimSetup.live_coordinates s thing angle distance h
  refine ⟨?_,?_,?_,?_,originX,originY,safeReads,separated⟩
  · exact congrArg (fun v => v.1) coords
  · exact congrArg (fun v => v.2.1) coords
  · exact congrArg (fun v => v.2.2.1) coords
  · exact congrArg (fun v => v.2.2.2.1) coords

/-- The firing ray's actual endpoint is carried into grid initialization without
assuming its coordinate correspondence a second time. -/
theorem first_aim_path_correspondence (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (setup : OriginalAimSetup.Inputs (E1M1AimQuery.firstRay gun s).core thing angle (Fixed.ofInt 1024))
    (originX : load32 (E1M1AimSetup.firstTraversal gun s).core.memory 0x2c104=ox.raw.toBitVec)
    (originY : load32 (E1M1AimSetup.firstTraversal gun s).core.memory 0x2c108=oy.raw.toBitVec)
    (safeReads : ∀ a, a ∈ OriginalPathInit.reads (E1M1AimSetup.firstTraversal gun s).core →
      ∀ b, b ∈ (OriginalPathInit.writes (E1M1AimSetup.firstTraversal gun s).core).toList → Apart a b)
    (separated : OriginalPathInit.Separated (E1M1AimSetup.firstTraversal gun s).core) :
    ∃ n, n≤223 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstPath gun s) ∧
    OriginalPathInit.Ready (E1M1AimSetup.firstTraversal gun s).core (firstPath gun s)
      (Collision.pathStart ox oy thing.x thing.y
        (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
        (thing.attackEndpoint angle (Fixed.ofInt 1024)).2) :=
  first_path_correspondence gun s f c h ox oy _ _ _ _
    (inputs_from_setup _ thing angle _ ox oy setup originX originY safeReads separated)
end Doom.Proofs.E1M1PathInit

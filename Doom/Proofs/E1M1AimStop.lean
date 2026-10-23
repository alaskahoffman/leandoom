import Doom.Proofs.E1M1AimWall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimStop
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWall (Safe returned)
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match E1M1FirstIntercept.program pc with
  | some op => some op
  | none => OriginalAimGuard.program pc

theorem contains_prior (pc : Nat) (h : E1M1FirstIntercept.program pc≠none) :
    program pc=E1M1FirstIntercept.program pc := by
  unfold program
  cases eq : E1M1FirstIntercept.program pc <;> simp_all

theorem contains_guard (pc : Nat) (h : OriginalAimGuard.program pc≠none) :
    program pc=OriginalAimGuard.program pc := by
  have range : (0x2b760≤pc ∧ pc<0x2b77f) ∨ (0x2b8d2≤pc ∧ pc<0x2b8db) := by
    by_cases a : 0x2b760≤pc ∧ pc<0x2b77f
    · exact Or.inl a
    · by_cases b : 0x2b8d2≤pc ∧ pc<0x2b8db
      · exact Or.inr b
      · simp [OriginalAimGuard.program,OriginalAimGuard.bytesProgram,a,b] at h
  rcases range with a|b
  · have all : ∀ i : Fin 31, program (0x2b760+i.val)=OriginalAimGuard.program (0x2b760+i.val) := by decide
    have eq : 0x2b760+(pc-0x2b760)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2b760,by omega⟩
  · have all : ∀ i : Fin 9, program (0x2b8d2+i.val)=OriginalAimGuard.program (0x2b8d2+i.val) := by decide
    have eq : 0x2b8d2+(pc-0x2b8d2)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2b8d2,by omega⟩

def result (s : X86Memory.State) := OriginalInterceptGate.resumed (returned s).core

/-- Complete one-sided callback, real RET, and the enclosing traversal's false
branch. No callback return value or post-return state is supplied. -/
theorem execution (s : X86Control.State) (hit : Collision.Intercept) (pointer : Word)
    (entry : s.pc=0x2b760) (returnWord : load32 s.core.memory (s.core.regs 4)=0x2c86d)
    (record : OriginalLineFinish.RecordAt s.core.memory (s.core.regs 0) hit pointer)
    (isLine : hit.isLine=true)
    (tagSafe : Safe (s.core.regs 4) (s.core.regs 0+4))
    (pointerSafe : Safe (s.core.regs 4) (s.core.regs 0+8))
    (flagsSafe : Safe (s.core.regs 4) (pointer+16))
    (oneSided : s.core.memory (pointer+16) &&& (4#8)=0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 24 s (result s.core) ∧
    (result s.core).pc=0x2c88c ∧ (result s.core).core.regs 0=0 ∧
    (result s.core).core.regs 4=s.core.regs 4+4 ∧
    (result s.core).core.memory=(OriginalAimGuard.saved s.core).memory := by
  have fields := E1M1AimWall.returned_fields s.core
  have head := (E1M1AimWall.execution s.core s.flags hit pointer record isLine tagSafe pointerSafe flagsSafe oneSided).transfer
    program [] contains_guard (by simp)
  rw [OriginalPathXStep.at_pc _ _ entry] at head
  have pc : (returned s.core).pc=0x2c86d := by rw [fields.2.2.2,returnWord]; rfl
  have tail := (X86CodeMemory.lift_success
    (OriginalInterceptGate.resume_execution (returned s.core).core (returned s.core).flags) FloorCaller.cm).transfer
    program [] (fun pc h => (contains_prior pc (by rw [E1M1FirstIntercept.contains_call pc h]; exact h)).trans
      (E1M1FirstIntercept.contains_call pc h)) (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have count : OriginalInterceptGate.resumeSteps (returned s.core).core=4 := by
    simp [OriginalInterceptGate.resumeSteps,fields.1]
  rw [count] at tail
  refine ⟨E1M1PspriteStep.prefix_trans head tail,?_,?_,?_,?_⟩
  all_goals simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.restored,fields.1,
    put,write,fields.2.1,fields.2.2.1]

/-- Use the selected record and return word from the previous reached-state
proof. Only the wall's map flags and static prologue separation remain inputs. -/
theorem from_ready (s : X86Control.State) (hits : Array Collision.Intercept)
    (resolve : Collision.Intercept → Word) (sp : Word)
    (ready : E1M1CallbackEntry.Ready hits resolve 0x2b760 sp s) :
    ∃ j, ∃ hi : j<hits.size,
      (hits[j].isLine=true →
       Safe (s.core.regs 4) (s.core.regs 0+4) →
       Safe (s.core.regs 4) (s.core.regs 0+8) →
       Safe (s.core.regs 4) (resolve hits[j]+16) →
       s.core.memory (resolve hits[j]+16) &&& (4#8)=0 →
       X86CodeMemory.Prefix FloorCaller.cm program [] 24 s (result s.core) ∧
       (result s.core).pc=0x2c88c ∧ (result s.core).core.regs 0=0 ∧
       (result s.core).core.regs 4=s.core.regs 4+4 ∧
       (result s.core).core.memory=(OriginalAimGuard.saved s.core).memory) := by
  obtain ⟨j,hi,record⟩ := E1M1CallbackEntry.selected_record hits resolve 0x2b760 sp s ready
  refine ⟨j,hi,?_⟩
  intro isLine tagSafe pointerSafe flagsSafe oneSided
  exact execution s hits[j] (resolve hits[j]) ready.pc ready.returnWord record isLine tagSafe pointerSafe flagsSafe oneSided
/-- Both executable paths stop on this same first one-sided wall. The map flag
encoding and ordered-path correspondence remain explicit interface premises. -/
theorem correspondence (s : X86Control.State) (hit : Collision.Intercept) (pointer : Word)
    (scene : Collision.Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (thing : Collision.SolidThing) (path : Collision.PathResult)
    (entry : s.pc=0x2b760) (returnWord : load32 s.core.memory (s.core.regs 4)=0x2c86d)
    (record : OriginalLineFinish.RecordAt s.core.memory (s.core.regs 0) hit pointer)
    (isLine : hit.isLine=true)
    (tagSafe : Safe (s.core.regs 4) (s.core.regs 0+4))
    (pointerSafe : Safe (s.core.regs 4) (s.core.regs 0+8))
    (flagsSafe : Safe (s.core.regs 4) (pointer+16))
    (flags : (s.core.memory (pointer+16) &&& (4#8) != 0)=scene.lines[hit.id]!.twoSided)
    (solid : scene.lines[hit.id]!.twoSided=false)
    (traced : E1M1AimSource.attackPath scene shooter angle distance=.ok (thing,path))
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 24 s (result s.core) ∧
    (result s.core).pc=0x2c88c ∧
    scene.aimLineAttack shooter angle distance=.ok {path:=E1M1AimSource.stopped path 1} := by
  have oneSided : s.core.memory (pointer+16) &&& (4#8)=0 := by simpa [solid] using flags
  have run := execution s hit pointer entry returnWord record isLine tagSafe pointerSafe flagsSafe oneSided
  exact ⟨run.1,run.2.1,E1M1AimSource.blocked_query scene shooter angle distance thing path hit
    traced nonempty first isLine solid⟩
end Doom.Proofs.E1M1AimStop

import Doom.Proofs.E1M1UseButton
import Doom.Proofs.OriginalPspriteStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Proofs.E1M1PspriteStep
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match PspriteStep.program pc with
  | some op => some op
  | none => E1M1UseButton.program pc


theorem contains_step (pc : Nat) (h : PspriteStep.program pc≠none) :
    program pc=PspriteStep.program pc := by
  unfold program
  cases eq : PspriteStep.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_use (pc : Nat) (h : E1M1UseButton.program pc≠none) :
    program pc=E1M1UseButton.program pc := by
  by_cases inside : 0x2dc60 ≤ pc ∧ pc < 0x2dc95
  · have checked : ∀ i : Fin 53, E1M1UseButton.program (0x2dc60+i.val)=none := by decide
    have e : 0x2dc60+(pc-0x2dc60)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2dc60,by omega⟩))
  · simp [program,PspriteStep.program,PspriteStep.bytesProgram,inside]

def result (s : X86Memory.State) : X86Control.State :=
  if UseButtonCode.requested s then UseButtonCode.result s
  else PspriteStep.result (PspriteStep.entered (UseButtonCode.result s).core).core

/-- Compose actual machine prefixes without using shared callee addresses as
whole-execution exits. The complete state at the seam is identical. -/
theorem prefix_trans {cm p stops n m s t u}
    (left : X86CodeMemory.Prefix cm p stops n s t)
    (right : X86CodeMemory.Prefix cm p stops m t u) :
    X86CodeMemory.Prefix cm p stops (n+m) s u := by
  induction left with
  | nil => simpa using right
  | @step n s middle last op len active decoded executed rest ih =>
    simpa only [Nat.succ_add] using X86CodeMemory.Prefix.step active decoded executed (ih right)

/-- A continuous instruction trace, including the actual setter CALL. A shared
callee can occur earlier in the trace, so it is not made a global stop address. -/
theorem append_step (s : X86Control.State) (before : X86Memory.State)
    (earlier : X86CodeMemory.run FloorCaller.cm E1M1UseButton.program UseButtonCode.exits 597 s=
      some (UseButtonCode.result before)) :
    ∃ n, n ≤ 620 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (result before) := by
  have tail : ∃ n, n ≤ 23 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      (UseButtonCode.result before) (result before) := by
    by_cases request : UseButtonCode.requested before
    · exact ⟨0,by omega,by simpa [result,request] using
        (X86CodeMemory.Prefix.nil (cm := FloorCaller.cm) (program := program) (exits := []) (UseButtonCode.result before))⟩
    · have segment := PspriteStep.execution (UseButtonCode.result before).core (UseButtonCode.result before).flags
      have pc : (UseButtonCode.result before).pc=0x2dc60 := by simp [UseButtonCode.result,request]
      have start : (UseButtonCode.result before)=⟨(UseButtonCode.result before).core,(UseButtonCode.result before).flags,0x2dc60⟩ := by rw [←pc]
      rw [←start] at segment
      obtain ⟨n,hn,path,_⟩ := X86Routine.run_path segment
      have path := (X86CodeMemory.lift_success path FloorCaller.cm).transfer program [] contains_step (by simp)
      exact ⟨n,hn,by simpa [result,request] using path⟩
  obtain ⟨n,hn,path,_⟩ := X86CodeMemory.run_path earlier
  have path := path.transfer program [] contains_use (by simp)
  obtain ⟨m,hm,tail⟩ := tail
  exact ⟨n+m,by omega,prefix_trans path tail⟩

theorem joined_execution (kind : FloorDamage.Kind) (s : X86Memory.State) (f : Option Flags)
    (motion : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (view : ViewState) (time : Int32) (cached : Bool) (floor : Fixed) (tick : Nat) (suit : Bool)
    (sim : Simulation) (map : sim.map.name="E1M1")
    (h : FloorJoined.Inputs kind s motion anim cmd timer view time cached true floor tick suit sim.rng)
    (v : PlayerDamage.State) (d : Int32) (body : Death.Body) (info : body.info=E1M1Death.playerInfo)
    (w : Fin 3) (y : Fixed)
    (contract : DamageTransport.Contract (E1M1FloorCycle.boundary kind s sim.rng).core v d
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim) body w y)
    (nonzero : FloorDamage.requested (E1M1FloorCycle.boundary kind s sim.rng)≠0)
    (readSafe : ∀ a, a ∈ DamageTransport.reads (E1M1FloorCycle.boundary kind s sim.rng).core w
      (E1M1FloorCycle.afterFloor kind motion.z floor tick suit sim).rng → a≠0x12720 →
      ∀ b, b ∈ E1M1PreparedFloor.prefixWrites s → Apart a b)
    (savedSafe : ∀ a, a ∈ SectorCaller.slots s →
      ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b)
    (buttons : BitVec 8) (choice : Fin 3) (selection : WeaponSelect.Inputs s buttons choice)
    (selectionSafe : ∀ a, a ∈ E1M1PlayerSelection.reads s choice → ∀ v, v ∈ E1M1PlayerSelection.priorWrites kind s sim.rng → Apart a v) :
    ∃ before : X86Control.State,
      X86CodeMemory.run FloorCaller.cm E1M1PlayerSelection.program [0x33476] 591 ⟨s,f,0x333b1⟩=
        some (WeaponSelect.result before.core buttons choice) ∧
      (∃ n, n ≤ 620 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x333b1⟩
        (result (WeaponSelect.result before.core buttons choice).core)) := by
  obtain ⟨before,run,gate⟩ := E1M1UseButton.joined_execution kind s f motion anim cmd timer view time cached floor tick suit sim map h
    v d body info w y contract nonzero readSafe savedSafe buttons choice selection selectionSafe
  exact ⟨before,run,append_step _ _ gate⟩

end Doom.Proofs.E1M1PspriteStep

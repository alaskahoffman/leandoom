import Doom.Proofs.E1M1PlayerSelection
import Doom.Proofs.OriginalUseButton
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Proofs.E1M1UseButton
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match UseButtonCode.program pc with
  | some op => some op
  | none => E1M1PlayerSelection.program pc

theorem contains_use (pc : Nat) (h : UseButtonCode.program pc≠none) :
    program pc=UseButtonCode.program pc := by
  unfold program
  cases eq : UseButtonCode.program pc with
  | none => exact False.elim (h eq)
  | some op => rfl

theorem contains_selection (pc : Nat) (h : E1M1PlayerSelection.program pc≠none) :
    program pc=E1M1PlayerSelection.program pc := by
  by_cases inside : 0x33476 ≤ pc ∧ pc < 0x334a9
  · have checked : ∀ i : Fin 51, E1M1PlayerSelection.program (0x33476+i.val)=none := by decide
    have e : 0x33476+(pc-0x33476)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x33476,by omega⟩))
  · simp [program,UseButtonCode.program,UseButtonCode.bytesProgram,inside]

/-- No additional use-gate contract: its result is proved for every byte and
32-bit latch value. The actual callee entry is the boundary, not a stubbed RET. -/
theorem append_use (s before : X86Control.State)
    (earlier : X86CodeMemory.run FloorCaller.cm E1M1PlayerSelection.program [0x33476] 591 s=some before)
    (pc : before.pc=0x33476) :
    X86CodeMemory.run FloorCaller.cm program UseButtonCode.exits 597 s=some (UseButtonCode.result before.core) := by
  have suffix := UseButtonCode.execution before.core before.flags
  have suffix : X86Routine.run UseButtonCode.program UseButtonCode.exits 6 before=some (UseButtonCode.result before.core) := by
    have e : before=⟨before.core,before.flags,0x33476⟩ := by rw [←pc]
    rw [e]; exact suffix
  obtain ⟨k,hk,path,done⟩ := X86Routine.run_path suffix
  have path := (X86CodeMemory.lift_success path FloorCaller.cm).transfer program UseButtonCode.exits contains_use (by
    intro a ha; simp only [UseButtonCode.exits,List.mem_cons,List.not_mem_nil,or_false,not_or]; constructor <;>
      intro e <;> subst a <;> exact ha (by decide))
  have tail : X86CodeMemory.run FloorCaller.cm program UseButtonCode.exits 6 before=some (UseButtonCode.result before.core) :=
    path.finish (fuel := 0) (by simp [X86CodeMemory.run,done]) 6 (by omega)
  obtain ⟨n,hn,path,_⟩ := X86CodeMemory.run_path earlier
  have path := path.transfer program UseButtonCode.exits contains_selection (by
    intro a ha; simp only [UseButtonCode.exits,List.mem_cons,List.not_mem_nil,or_false,not_or]; constructor <;>
      intro e <;> subst a <;> exact ha (by decide))
  exact path.finish tail 597 (by omega)

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
      X86CodeMemory.run FloorCaller.cm program UseButtonCode.exits 597 ⟨s,f,0x333b1⟩=
        some (UseButtonCode.result (WeaponSelect.result before.core buttons choice).core) := by
  obtain ⟨before,_,run,_⟩ := E1M1PlayerSelection.joined_execution kind s f motion anim cmd timer view time cached floor tick suit sim map h
    v d body info w y contract nonzero readSafe savedSafe buttons choice selection selectionSafe
  exact ⟨before,run,append_use _ _ run (WeaponSelect.result_pc _ _ _)⟩

/-- The live adapter writes only the pending-weapon field, even with zero health. -/
theorem runtime_selection (s : Simulation) (keys : UInt32) :
    (s.selectWeapon keys).inventory.pickupState.pendingWeapon=
      (({player := s.inventory.toPickup} : Weapon.Context).select
        (if keyDown keys 16384 then some 0 else if keyDown keys 32768 then some 1
          else if keyDown keys 65536 then some 2 else none)).player.pendingWeapon ∧
    (s.selectWeapon keys).inventory.health=s.inventory.health ∧
    (s.selectWeapon keys).useHeld=s.useHeld := by exact ⟨rfl,rfl,rfl⟩

end Doom.Proofs.E1M1UseButton

import Doom.Proofs.E1M1FloorReturn
open Doom Doom.Proofs Doom.Verification X86 X86Memory
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
/-- Witnesses for the new separation contracts only; these are not assertions
that an entire arbitrary zero-memory game state satisfies the gameplay inputs. -/
def fixture (sp : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600080 else if r=4 then sp else 0,fun _ => 0⟩
example (sp : Word) (h : sp=0x700080 ∨ sp=0) : E1M1FloorReturn.Inputs (fixture sp) := by
  rcases h with rfl|rfl <;> constructor <;>
    simp [E1M1DeathTiming.returnWrites,E1M1DeathTiming.stackWrites,E1M1FloorReturn.allWrites,
      E1M1DeathTiming.previousWrites,E1M1DeathTiming.timingWrites,
      E1M1DeathSetter.returnWrites,E1M1DeathSetter.stackWrites,E1M1DeathSetter.previousWrites,E1M1DeathSetter.suffixWrites,
      KillDeathBranches.returnWrites,KillDeathBranches.stackWrites,KillDeathBranches.priorWrites,
      KillWeaponDrop.returnWrites,KillWeaponDrop.stackWrites,KillWeaponDrop.priorWrites,KillWeaponDrop.dropView,
      KillBookkeeping.returnWrites,KillBookkeeping.stackWrites,KillBookkeeping.writes,KillBookkeeping.priorWrites,
      KillBookkeeping.entryView,KillBookkeeping.player,KillBookkeeping.fragAddress,
      KillEntry.returnWrites,KillEntry.stackWrites,KillEntry.suffixWrites,KillEntry.callSlots,
      ActorHealth.afterWrites,ActorHealth.joinedWrites,ActorHealth.callSlots,
      PlayerHealth.afterWrites,PlayerHealth.writes,WeaponDrop.writes,WeaponDrop.psp,
      DeathSetter.fields,PainSetter.fields,PlayerDamageEntry.inputPlayer,PlayerDamageEntry.writes,PlayerDamageEntry.slots,fixture,write,load32] <;> (repeat' apply And.intro) <;> simp only [BlockSummary.Apart] <;> decide

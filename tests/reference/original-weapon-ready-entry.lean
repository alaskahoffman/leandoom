import Doom.Proofs.E1M1WeaponReadyEntry
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.ReadyEntryFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def p : Word := 0x600101
def obj : Word := 0x600501
def slot : Word := p+244
def table : Word := 0x15a28+28*10
def memory (frame : Nat) (w ps : Word) : Memory :=
  ([(p,obj),(obj+100,BitVec.ofNat 32 (0x15a28+28*frame)),(p+112,w),(p+116,10),
    (p+32,100),(slot,ps),(slot+12,38*65536),(0x12db4,10),
    (table+8,1),(table+12,0x2d2f0),(table+16,10),
    (1,0x2d095),(5,0),(9,slot),(13,0x2dc95)] : List (Word × Word)).foldl
      (fun m pair => store32 m pair.1 pair.2) (fun _ => 0)
def initial (frame : Nat) (w ps : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then p else if r=2 || r=3 then slot else if r=4 then 1 else 0,memory frame w ps⟩

example : WeaponReadyEntry.Inputs (initial 149 1 table) 149 1 := by constructor <;> decide
example : WeaponReadyEntry.Inputs (initial 154 2 table) 154 2 := by constructor <;> decide
example : (WeaponReadyEntry.result (initial 149 1 table)).pc=0x2d333 := by decide
example : (WeaponReadyEntry.result (initial 154 1 table)).pc=0x30ea0 := by decide
example : (WeaponReadyEntry.result (initial 155 1 table)).pc=0x30ea0 := by decide
example : (WeaponReadyEntry.result (initial 149 7 0x1617c)).pc=0x3f370 := by decide
example : (WeaponReadyEntry.result (initial 149 7 table)).pc=0x2d333 := by decide
example : (WeaponReadyEntry.result (initial 154 1 table)).core.regs 2=149 := by decide
example : load32 (WeaponReadyEntry.result (initial 154 1 table)).core.memory 0xffffffed=0x2d319 := by decide

def raised := E1M1WeaponReady.raiseNext (initial 149 1 table)
def bobEntry := WeaponReadyEntry.prepared raised.core
example : raised.pc=0x2d2f0 := by decide
theorem raised_inputs : WeaponReadyEntry.Inputs raised.core 149 1 := by constructor <;> decide
theorem not_lowering : ¬WeaponReadyGate.lowering bobEntry := by decide
theorem no_attack : WeaponReadyGate.attack bobEntry=0 := by decide

def final := (E1M1WeaponReady.raisedIdleReturn bobEntry).getD ⟨initial 149 1 table,none,0⟩
theorem returns : E1M1WeaponReady.raisedIdleReturn bobEntry=some final := by
  have good : (E1M1WeaponReady.raisedIdleReturn bobEntry).isSome=true := by decide
  unfold final
  generalize E1M1WeaponReady.raisedIdleReturn bobEntry=r at *
  cases r <;> simp_all
example : final.pc=0x2dc95 ∧ final.core.regs 4=17 := by decide
example : ∃ n, n≤133 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyEntry.program [] n
    ⟨initial 149 1 table,none,0x2d4d0⟩ final :=
  E1M1WeaponReadyEntry.raise_idle_return _ _ 149 1 (by decide) raised_inputs (by decide) not_lowering no_attack final returns
end Doom.Verification.ReadyEntryFixture

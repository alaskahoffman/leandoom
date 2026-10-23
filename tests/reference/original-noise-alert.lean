import Doom.Proofs.E1M1NoiseAlert
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.NoiseAlertFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def sector : Word := 0x600201
def initial (count stamp cost blocks lines : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then sector else if r=2 then blocks else if r=4 then 1 else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,count),(0x2b958,0x600801),(sector+66,stamp),(sector+18,cost),(sector+78,lines)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩
def fresh := initial 5 4 0 0 3
def better := initial 5 5 2 0 3
def skip := initial 5 5 1 0 3
def empty := initial 5 4 0 0 0
example : (E1M1NoiseAlert.sectorResult fresh).pc=0x26fa6 ∧
    load32 (E1M1NoiseAlert.sectorResult fresh).core.memory (sector+66)=5 ∧
    load32 (E1M1NoiseAlert.sectorResult fresh).core.memory (sector+18)=1 ∧
    load32 (E1M1NoiseAlert.sectorResult fresh).core.memory (sector+22)=0x600801 ∧
    (E1M1NoiseAlert.sectorResult fresh).core.regs 4=0xffffffe9 := by decide
example : (E1M1NoiseAlert.sectorResult better).pc=0x26fa6 ∧
    load32 (E1M1NoiseAlert.sectorResult better).core.memory (sector+18)=1 := by decide
example : (E1M1NoiseAlert.sectorResult skip).pc=0x27011 ∧
    load32 (E1M1NoiseAlert.sectorResult skip).core.memory (sector+22)=0 := by decide
example : (E1M1NoiseAlert.sectorResult empty).pc=0x27011 ∧
    load32 (E1M1NoiseAlert.sectorResult empty).core.memory (sector+22)=0x600801 := by decide
-- Signed wrap makes this raw state revisit; reachability is a separate obligation.
example : (E1M1NoiseAlert.sectorResult (initial 5 5 0 0x7fffffff 1)).pc=0x26fa6 ∧
    load32 (E1M1NoiseAlert.sectorResult (initial 5 5 0 0x7fffffff 1)).core.memory (sector+18)=0x80000000 := by decide

def alert : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600801 else if r=2 then 0x600401 else if r=4 then 1 else 0,
    ([(0x600401+52,0x600101),(0x600101,sector),(0x13580,0xffffffff),
      (sector+66,0xffffffff),(sector+78,3)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩
example : load32 (NoiseAlert.result alert).core.memory 0x13580=0 ∧
    (NoiseAlert.result alert).core.regs 0=sector ∧ (NoiseAlert.result alert).core.regs 2=0 := by decide
example : ∃ n, n≤32 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseAlert.program [] n
    ⟨alert,none,0x27020⟩ (E1M1NoiseAlert.result alert) := E1M1NoiseAlert.alert_execution _ _
example : load32 (E1M1NoiseAlert.result alert).core.memory (sector+22)=0x600801 := by decide
-- Aliased subsector reads must observe the preceding soundtarget store.
def alias : X86Memory.State :=
  {alert with memory := store32 alert.memory (0x600401+52) 0x2b958}
example : (NoiseAlert.result alias).core.regs 0=0x600801 := by decide
end Doom.Verification.NoiseAlertFixture

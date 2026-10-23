"""Opt-in active icon: explicit devices, no fabricated helper return."""
import sys, unittest
sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
import test_e1m1_aim_read_prologue as prior
ROOT = prior.ROOT
class ActiveIconTests(unittest.TestCase):
    lean = prior.AimReadPrologueTests.lean
    succeeds = prior.AimReadPrologueTests.succeeds
    rejects = prior.AimReadPrologueTests.rejects
    def test_opt_in_device_instructions_and_fail_closed(self):
        self.assertTrue((ROOT/'Doom/Verification/X86VgaRoutine.lean').exists(), 'explicit opt-in device semantics missing')
        self.succeeds('''import Doom.Verification.X86VgaRoutine
open Doom.Verification X86VgaRoutine
example : decode [0xb0,2] = some (.byteImmediate 0 2,[]) := by decide +kernel
example : decode [0xee] = some (.output,[]) := by decide +kernel
example : decode [0xec] = some (.input,[]) := by decide +kernel
example : decode [0xcd,0x21] = none := by decide +kernel
example (env : Environment) (s : X86VgaRoutine.State) (h : s.ioAllowed=false) :
    execute env .input s=none := by
  change (if (s.ioAllowed && knownPort (port s)) = true then _ else _) = none
  rw [h]
  rfl
example (env : Environment) (s : X86VgaRoutine.State) (h : s.apertureMapped=false) :
    execute env (.loadByte 1 ⟨some 0,none,0,0⟩) s=none := by
  change (if (s.apertureMapped && aperture _) = true then _ else _) = none
  rw [h]
  rfl
example (env : Environment) (op : X86VgaRoutine.Op) (s t : X86VgaRoutine.State)
    (h : execute env op s=some t) : t.cpu.core.memory=s.cpu.core.memory := by
  exact execute_memory env op s t h
''')
    def test_active_head_reaches_first_copy_for_every_device(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimActiveIcon.lean').exists(), 'actual active instruction path missing')
        self.succeeds('''import Doom.Proofs.E1M1AimActiveIcon
#check Doom.Proofs.E1M1AimActiveIcon.decoded
#check Doom.Proofs.E1M1AimActiveIcon.head_execution
''')
    def test_copy_loop_body_has_real_instruction_steps(self):
        self.succeeds('''import Doom.Proofs.E1M1AimActiveIcon
#check Doom.Proofs.E1M1AimActiveIcon.copy_body_execution
#check Doom.Proofs.E1M1AimActiveIcon.copy_body_registers
''')
    def test_both_copy_loops_terminate_without_device_values(self):
        self.succeeds('''import Doom.Proofs.E1M1AimActiveIcon
#check Doom.Proofs.E1M1AimActiveIcon.copy_back_body_execution
#check Doom.Proofs.E1M1AimActiveIcon.copy_loop_execution
''')
    def test_active_hardware_tail_executes_pops_and_ret(self):
        self.succeeds('''import Doom.Proofs.E1M1AimActiveIcon
#check Doom.Proofs.E1M1AimActiveIcon.tail_execution
#check Doom.Proofs.E1M1AimActiveIcon.tail_registers
''')
    def test_full_active_execution_preserves_ram_and_returns(self):
        self.succeeds('''import Doom.Proofs.E1M1AimActiveIcon
#check Doom.Proofs.E1M1AimActiveIcon.execution
''')
if __name__=='__main__': unittest.main()

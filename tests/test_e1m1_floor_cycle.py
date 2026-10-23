"""Pinned floor epilogues, continuous caller composition, and fail-closed checks."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_floor_cycle as proof


class E1M1FloorCycleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = json.loads((ROOT/'tests/reference/original-floor-return.json').read_text())
        cls.exe = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary = proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip', sw, cls.exe)
        cls.raw = proof.extraction.extract(cls.binary, cls.exe, cls.spec)

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'Check.lean'; path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)], cwd=ROOT, capture_output=True, text=True)

    def reject(self, pairs):
        source = proof.certificate(self.raw)
        for old, new in pairs:
            with self.subTest(change=new):
                self.assertIn(old, source)
                result = self.lean(source.replace(old, new))
                self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
                self.assertIn('error:', result.stdout)

    def test_certificate_and_strict_audit(self):
        result = self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound', 'sorryAx'), result.stdout.replace('Quot.sound', 'bad._native.ax_1'),
                    result.stdout+'unexpected', result.stdout.replace('lift_success', 'missing')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_each_original_epilogue_is_bound(self):
        for name in 'abcd':
            with self.subTest(unit=name):
                raw = dict(self.raw); data = bytearray(raw[name]); data[0] ^= 1; raw[name] = bytes(data)
                result = self.lean(proof.certificate(raw))
                self.assertNotEqual(result.returncode, 0); self.assertIn('decide', result.stdout)

    def test_pop_order_and_return_are_bound(self):
        for offset in [1, 2, 3, 4]:
            with self.subTest(offset=offset):
                raw = dict(self.raw); data = bytearray(raw['a']); data[offset] ^= 1; raw['a'] = bytes(data)
                result = self.lean(proof.certificate(raw))
                self.assertNotEqual(result.returncode, 0); self.assertIn('decide', result.stdout)

    def test_entry_return_stack_and_saved_registers(self):
        self.reject([('[0x333e5] 342', '[0x333e4] 342'), ('⟨s,f,0x333d0⟩', '⟨s,f,0x333de⟩'),
                     ('t.core.regs 4=s.regs 4', 't.core.regs 4=s.regs 4+4'),
                     ('t.core.regs 2=s.regs 2', 't.core.regs 2=s.regs 1')])

    def test_floor_contract_and_post_floor_rng_required(self):
        self.reject([('(floorInputs : FloorCaller.Inputs kind s z floor time suit sim.rng)', '(floorInputs : True)'),
                     ('(E1M1FloorCycle.afterFloor kind z floor time suit sim).rng', 'sim.rng'),
                     ('(timing : E1M1DeathTiming.Inputs (E1M1FloorCycle.boundary kind s sim.rng).core (E1M1FloorCycle.afterFloor kind z floor time suit sim).rng)', '(timing : True)')])

    def test_initial_saved_frame_separation_required(self):
        self.reject([('(safe : ∀ a, a ∈ SectorCaller.slots s → ∀ b, b ∈ E1M1FloorReturn.allWrites (E1M1FloorCycle.boundary kind s sim.rng).core → Apart a b)', '(safe : True)'),
                     ('(returnPC : load32 s.memory (s.regs 4+16)=0x333e5)', '(returnPC : True)')])

    def test_original_mapping_and_relocations_checked(self):
        for name, field, value in [('a', 'file_offset', '0x0'), ('d', 'code_offset', '0x2fc3a'),
                                   ('c', 'relocations', [{'offset':0, 'object':3, 'target':'0x0'}])]:
            with self.subTest(field=field):
                bad = copy.deepcopy(self.spec); bad['units'][name][field] = value
                with self.assertRaises(ValueError): proof.extraction.extract(self.binary, self.exe, bad)

    def test_success_bridge_with_unexecuted_code_jump(self):
        source = '''import Doom.Verification.X86CodeBridge
open Doom.Verification X86 X86Memory X86Control
-- A CS jump exists in the program, but the proved path jumps over it.
def p : X86Routine.Program
  | 0 => some (.jump 1,1)
  | 1 => some (.jumpCode ⟨none,none,0,0⟩,1)
  | _ => none
example (cm : Memory) (s : X86Memory.State) (f : Option Flags) :
    X86CodeMemory.run cm p [2] 1 ⟨s,f,0⟩=some ⟨s,f,2⟩ := by
  apply X86CodeMemory.run_lift_success
  simp [X86Routine.run,p,X86Routine.execute]
'''
        result = self.lean(source)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_outer_separation_witnesses(self):
        result = self.lean((ROOT/'tests/reference/e1m1-floor-cycle-separation.lean').read_text())
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertEqual(result.stdout, '')


if __name__ == '__main__': unittest.main()

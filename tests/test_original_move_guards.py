"""Original movement guard certificates, instruction flags, and failure boundaries."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_move_guards as guards


class OriginalMoveGuardTests(unittest.TestCase):
    def lean(self, source):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'Guards.lean'; path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True, timeout=90)

    def units(self):
        spec = json.loads((ROOT/'tests/reference/original-move-guards.json').read_text())
        return {name: bytes.fromhex(u['hex']) for name, u in spec['units'].items()}

    def test_certificate_audits(self):
        result = self.lean(guards.certificate(self.units(), 'synthetic regression'))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        guards.audit(result.stdout)
        for text in [result.stdout.replace('Quot.sound', 'sorryAx'),
                     result.stdout.splitlines()[0], result.stdout+'\nextra theorem']:
            with self.assertRaises(ValueError): guards.audit(text)

    def test_changed_comparison_and_branch_targets_rejected(self):
        for name, offset, value in [('forwardGuardBytes', 9, 0x9c), # SETL instead of SETLE
                                    ('forwardGuardBytes', 25, 0x75), # JNE instead of JE
                                    ('sideGuardBytes', 6, 0x55)]: # wrong skip target
            with self.subTest(name=name, offset=offset):
                units = self.units(); raw = bytearray(units[name]); raw[offset] = value; units[name] = bytes(raw)
                result = self.lean(guards.certificate(units, 'deliberate mutation'))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('is false', result.stdout)
                with self.assertRaises(ValueError): guards.audit(result.stdout)

    def test_flags_byte_registers_and_failure_boundaries(self):
        result = self.lean('''import Doom.Proofs.OriginalMoveGuards
open Doom.Verification X86 X86Memory X86Control
example : (compare32 (0x80000000#32) (1#32)).lessEqual = true := by decide
example : (compare32 (0x7fffffff#32) (0xffffffff#32)).lessEqual = false := by decide
example (s : X86Memory.State) :
  X86Control.execute (.jumpZero true 2) ⟨s, none, 0⟩ = none := rfl
example (s : X86Memory.State) :
  X86Control.execute (.setle 0) ⟨s, none, 0⟩ = none := rfl
example : blockPreservesFlags (.arithmetic (.add 0 3)) = false := rfl
example : blockPreservesFlags (.legacy (.mov 0 3)) = true := rfl
example : blockPreservesFlags (.shr 2 0) = true := rfl
example : blockPreservesFlags (.shr 2 1) = false := rfl
example : X86Control.decode [0xe8, 0, 0, 0, 0] = none := by decide
example : X86Control.decode [0x74] = none := by decide
example : X86Control.decode [0x66, 0x85, 0xc0] = none := by decide
example : X86Control.decode [0x83, 0x05, 0, 0, 0, 0, 0] = none := by decide
example (s : X86Memory.State) : X86Control.run Doom19.forwardGuardBytes [31,103] 0 ⟨s, none, 0⟩ = none := rfl
-- A negative branch target is rejected, not silently clamped to address zero.
example (s : X86Memory.State) :
  X86Control.execute (.jumpZero true (-5)) ⟨s, some ⟨true,false,false,none⟩, 2⟩ = none := by rfl
-- DL and DH independently preserve their neighboring byte and upper word.
example (a : BitVec 32) (v : BitVec 8) :
  (((a &&& (0xffffff00#32)) ||| v.zeroExtend 32).extractLsb' 8 24) = a.extractLsb' 8 24 := by bv_decide
example (a : BitVec 32) (v : BitVec 8) :
  (((a &&& (0xffff00ff#32)) ||| (v.zeroExtend 32 <<< 8)).extractLsb' 0 8) = a.extractLsb' 0 8 := by bv_decide
''')
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_original_extraction(self):
        spec = json.loads((ROOT/'tests/reference/original-move-guards.json').read_text())
        profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
        shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        archive = ROOT/shareware['local_directory']/'doom19s.zip'
        if not archive.exists(): self.skipTest('shareware archive not installed')
        binary = guards.original.extract(archive, shareware, profile)
        self.assertEqual(guards.extract(binary, profile, spec), self.units())
        bad = json.loads(json.dumps(spec)); bad['units']['sideGuardBytes']['file_offset'] = '0x0'
        with self.assertRaisesRegex(ValueError, 'file mapping'): guards.extract(binary, profile, bad)


if __name__ == '__main__': unittest.main()

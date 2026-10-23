"""Certificates reject changed original bytes and false block summaries."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_thrust as thrust


class OriginalThrustTests(unittest.TestCase):
    def lean(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'Thrust.lean'
            path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def test_certificate_and_axiom_audit(self):
        raw = bytes.fromhex(json.loads((ROOT/'tests/reference/original-thrust.json').read_text())['hex'])
        result = self.lean(thrust.certificate(raw, 'synthetic test'))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        thrust.audit(result.stdout)
        for changed in [result.stdout.replace('Quot.sound', 'sorryAx'),
                        result.stdout.splitlines()[0], result.stdout+'\nextra theorem']:
            with self.assertRaises(ValueError): thrust.audit(changed)

    def test_mutated_angle_shift_table_and_momentum_address(self):
        raw = bytes.fromhex(json.loads((ROOT/'tests/reference/original-thrust.json').read_text())['hex'])
        for offset, value in [(6, 18), (40, 0x88), (54, 0x48)]:
            with self.subTest(offset=offset):
                mutated = bytearray(raw); mutated[offset] = value
                result = self.lean(thrust.certificate(mutated, 'deliberate mutation'))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('code = Doom19.playerThrustBytes', result.stdout)
                self.assertIn('is false', result.stdout)
                with self.assertRaises(ValueError): thrust.audit(result.stdout)

    def test_decoder_and_composition(self):
        result = self.lean('''import Doom.Proofs.BlockSummary
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Doom.Verification Doom.Verification.X86 Doom.Verification.X86Memory
open Doom.Verification.X86Block Doom.Proofs.BlockSummary
-- Unsupported control flow, prefixes, and truncated operands fail closed.
example : decodeBlock 1 [0xeb, 0x00] = none := by decide
example : decodeBlock 1 [0x66, 0x89, 0xc1] = none := by decide
example : decodeBlock 1 [0x8b, 0x1d, 0x84] = none := by decide
example : decodeBlock 1 [0x8b, 0x04] = none := by decide
example : decodeBlock 0 [0x90] = none := by decide
example : decodeBlock 2 [0x89, 0xc1] = none := by decide
-- SIB, sign-extended disp8, and disp32 are interpreted distinctly.
example : decodeBlock 1 [0x8b, 0x44, 0x88, 0xfc] =
  some [.load 0 ⟨some 0, some 1, 2, -4⟩] := by decide
example : decodeBlock 1 [0x8b, 0x05, 0x84, 0x35, 1, 0] =
  some [.load 0 ⟨none, none, 0, 0x13584⟩] := by decide
example (a b : List X86Block.Op) (s : State) :
  eval (a ++ b) s = summarized b (summarized a s) := by
  rw [eval_append]
  exact (summarized_correct b (eval a s)).trans
    (congrArg (summarized b) (summarized_correct a s))
-- The summary tactic also works on the earlier turning block without a listing.
def turnOps := (decodeBlock 6 Doom19.playerTurnBytes).getD []
example (s : State) : (X86Block.run 6 Doom19.playerTurnBytes s).map (·.memory) =
    some (store32 s.memory (load32 s.memory (s.regs eax) + 32)
      (load32 s.memory (load32 s.memory (s.regs eax) + 32) +
       ((load16 s.memory (s.regs eax + 10)).signExtend 32 <<< 16))) := by
  rw [certified Doom19.playerTurnBytes turnOps 6 (by rfl)]
  summarize_x86 turnOps
''')
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_false_summary_is_not_accepted(self):
        # Genuine multiplication bytes with a deliberately wrong result claim.
        result = self.lean('''import Doom.Proofs.BlockSummary
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open Doom.Verification Doom.Verification.X86 Doom.Verification.X86Memory
open Doom.Verification.X86Block Doom.Proofs.BlockSummary
example (s : State) : (X86Block.run 2 Doom19.fixedMulBytes s).map (·.memory) =
    some (store32 s.memory 0 0) := by
  rw [certified Doom19.fixedMulBytes [.arithmetic (.imul 3), .arithmetic (.shrd 0 2 16)] 2 (by rfl)]
  simp [summarized, multiply]
''')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('unsolved goals', result.stdout)

    def test_extraction_and_complete_table(self):
        spec = json.loads((ROOT/'tests/reference/original-thrust.json').read_text())
        profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
        shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        archive = ROOT/shareware['local_directory']/'doom19s.zip'
        if not archive.exists(): self.skipTest('shareware archive not installed')
        binary = thrust.original.extract(archive, shareware, profile)
        raw, table = thrust.extract(binary, profile, spec)
        self.assertEqual(len(raw), 55)
        self.assertEqual(thrust.check_tables(table)['entries'], 10240)
        changed = dict(spec, relocations=[])
        with self.assertRaisesRegex(ValueError, 'relocation identity'):
            thrust.extract(binary, profile, changed)
        mutated = bytearray(table); mutated[0] ^= 1
        with self.assertRaisesRegex(ValueError, 'table mismatch'):
            thrust.check_tables(mutated)


if __name__ == '__main__': unittest.main()

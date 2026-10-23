"""Continuous original-byte certificates and composition failure boundaries."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_move_entry as entry


class OriginalMoveEntryTests(unittest.TestCase):
    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/original-move-entry.json').read_text())
        self.raw = bytes.fromhex(self.spec['units']['moveEntryBytes']['hex'])

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'Entry.lean'; p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(p)],
                                  cwd=ROOT, capture_output=True, text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result = self.lean(entry.certificate(self.raw, 'test'))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        entry.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound', 'sorryAx'),
                    result.stdout.replace('Quot.sound', 'unverified._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0], result.stdout+'\nextra']:
            with self.assertRaises(ValueError): entry.audit(bad)

    def test_broken_command_pointer_turn_and_branch_rejected(self):
        for offset, value in [(4, 9), (13, 15), (43, 75)]:
            with self.subTest(offset=offset):
                changed = bytearray(self.raw); changed[offset] = value
                result = self.lean(entry.certificate(changed, 'mutation'))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('is false', result.stdout)
                with self.assertRaises(ValueError): entry.audit(result.stdout)

    def test_composition_and_relocation_failure_boundaries(self):
        result = self.lean('''import Doom.Proofs.OriginalMoveEntry
open Doom.Verification Doom.Verification.X86 Doom.Verification.X86Memory
open Doom.Verification.X86Control
-- The relocated program is undefined below its base, not a truncated subtraction.
example : shiftProgram 17 Doom.Proofs.forwardGuardProgram 0 = none := by decide
example : shiftProgram 17 Doom.Proofs.forwardGuardProgram 17 =
    Doom.Proofs.forwardGuardProgram 0 := by rfl
-- Relocation theorem excludes backward jumps; underflow can change success.
example : ¬ ForwardOp (.jumpZero true (-1)) := by simp [ForwardOp]
def s : X86Control.State := ⟨⟨fun _ => 0, fun _ => 0⟩, some ⟨true, false, false,none⟩, 0⟩
example : execute (.jumpZero true (-1)) s = none := by decide
example : (execute (.jumpZero true (-1)) (shiftState 1 s)).map (·.pc) = some 0 := by decide
-- An enclosing exit stops before executing a proposed prefix instruction.
example : (runProgram Doom.Proofs.moveEntryProgram [0] 17 s).map (·.pc) = some 0 := by rfl
example : runProgram Doom.Proofs.moveEntryProgram [48,120] 0 s = none := by rfl
example (core : X86Memory.State) (flags : Option Flags) :
    runProgram Doom.Proofs.moveEntryProgram [48,120] 17 ⟨core,flags,0⟩ =
      runProgram Doom.Proofs.moveEntryProgram [48,120] 11
        ⟨Doom.Proofs.turnEndCore core,none,17⟩ :=
  (Doom.Proofs.move_entry_turn_prefix core flags).run 11
''')
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_arbitrary_state_cannot_be_inserted_at_seam(self):
        result = self.lean('''import Doom.Verification.X86Compose
open Doom.Verification.X86Control
example (program : Program) (s t : State) : Prefix program [] 0 s t := by
  exact Prefix.nil s
''')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('mismatch', result.stdout.lower())

    def test_contiguous_extraction_and_relocation_rejection(self):
        profile = json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        archive = ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists(): self.skipTest('shareware archive not installed')
        binary = entry.original.extract(archive, sw, profile)
        self.assertEqual(entry.extraction.extract(binary, profile, self.spec)['moveEntryBytes'], self.raw)
        for key, value, message in [('file_offset','0x0','mapping'),('relocations',[],'relocation')]:
            changed = json.loads(json.dumps(self.spec)); changed['units']['moveEntryBytes'][key] = value
            with self.assertRaisesRegex(ValueError, message): entry.extraction.extract(binary,profile,changed)


if __name__ == '__main__': unittest.main()

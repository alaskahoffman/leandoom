"""Original inlined movement certificates, failure paths and decoder boundaries."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_inline_thrust as inline


class OriginalInlineThrustTests(unittest.TestCase):
    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/original-inline-thrust.json').read_text())
        self.units = {n: bytes.fromhex(u['hex']) for n, u in self.spec['units'].items()}

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'Inline.lean'; p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(p)],
                                  cwd=ROOT, capture_output=True, text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result = self.lean(inline.certificate(self.units, 'test'))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        inline.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound', 'sorryAx'),
                    result.stdout.replace('Quot.sound', 'unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0], result.stdout+'\nextra']:
            with self.assertRaises(ValueError): inline.audit(bad)

    def test_changed_byte_register_angle_and_stack_operand_rejected(self):
        for name, offset, value in [('forwardThrustBytes', 15, 0xfe),
                                     ('forwardThrustBytes', 29, 0x08),
                                     ('sideThrustBytes', 9, 0x20)]:
            with self.subTest(name=name, offset=offset):
                changed = dict(self.units); b = bytearray(changed[name]); b[offset] = value; changed[name] = b
                result = self.lean(inline.certificate(changed, 'mutation'))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('is false', result.stdout)
                with self.assertRaises(ValueError): inline.audit(result.stdout)

    def test_instruction_semantics_and_failure_boundaries(self):
        result = self.lean('''import Doom.Proofs.OriginalInlineThrust
import Doom.Verification.X86Control
open Doom.Verification Doom.Verification.X86 Doom.Verification.X86Memory
open Doom.Verification.X86Block
example : decodeBlock 1 [0x0f, 0xbe, 0xfa] = some [.movsx8 7 2] := by decide
example : decodeBlock 1 [0x0f, 0xbe, 0xfe] = some [.movsx8 7 6] := by decide
example : decodeBlock 1 [0x0f, 0xbe, 0x3a] = none := by decide
example : decodeBlock 1 [0x0f, 0xbe] = none := by decide
example : decodeBlock 1 [0x2d, 0, 0, 0] = none := by decide
example : decodeBlock 1 [0x66, 0x2d, 0, 0, 0, 0x40] = none := by decide
example : decodeBlock 1 [0x89, 0x04] = none := by decide
example : decodeBlock 1 [0x89, 0x04, 0x24] =
  some [.store ⟨some 4, none, 0, 0⟩ 0] := by decide
example : decodeBlock 1 [0x2d, 0, 0, 0, 0x40] = some [.subEax 0x40000000] := by decide
-- DL and DH are signed bytes of EDX, never ESI or the whole EDX value.
def state : State := ⟨fun _ => 0x1234807f, fun _ => 0⟩
example : (X86Block.execute (.movsx8 7 2) state).regs 7 = 127 := by decide
example : (X86Block.execute (.movsx8 7 6) state).regs 7 = 0xffffff80 := by decide
example : (X86Block.execute (.movsx8 7 6) state).regs edx = 0x1234807f := by decide
example : (X86Block.execute (.subEax 0x40000000) state).regs eax = 0xd234807f := by decide
example : X86Control.blockPreservesFlags (.movsx8 7 6) = true := by decide
example : X86Control.blockPreservesFlags (.store ⟨some 4, none, 0, 0⟩ 0) = true := by decide
example : X86Control.blockPreservesFlags (.subEax 0x40000000) = false := by decide
-- Ordered raw memory theorem remains applicable even if scratch overlaps a
-- game field; the engine-correspondence theorem requires explicit separation.
example (s : State) :
    (X86Block.run 23 Doom19.forwardThrustBytes s).map (·.memory) =
      some (Doom.Proofs.inlineThrustMemory s false) := Doom.Proofs.original_forward_thrust_memory s
''')
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_pinned_extraction_and_relocation_rejection(self):
        profile = json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        archive = ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists(): self.skipTest('shareware archive not installed')
        binary = inline.original.extract(archive, sw, profile)
        self.assertEqual(inline.extract(binary, profile, self.spec), self.units)
        for key, value, message in [('file_offset', '0x0', 'mapping'), ('relocations', [], 'relocation')]:
            changed = json.loads(json.dumps(self.spec))
            changed['units']['forwardThrustBytes'][key] = value
            with self.assertRaisesRegex(ValueError, message): inline.extract(binary, profile, changed)


if __name__ == '__main__': unittest.main()

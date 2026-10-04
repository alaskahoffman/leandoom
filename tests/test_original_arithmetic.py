"""Kernel certificates must reject changed branch instructions and RNG data."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_arithmetic as arithmetic


class OriginalArithmeticTests(unittest.TestCase):
    def test_axiom_audit_accepts_wrapped_output(self):
        output = '\n'.join(
            f"'Doom.Verification.ExtractedArithmetic.extracted_{name}' depends on axioms: "
            '[propext,\n Classical.choice,\n Quot.sound]'
            for name in ['add','sub','div','random_trace'])
        arithmetic.audit(output)

    def test_axiom_audit_rejects_untrusted_or_incomplete_output(self):
        output = '\n'.join(
            f"'Doom.Verification.ExtractedArithmetic.extracted_{name}' depends on axioms: [propext, Quot.sound]"
            for name in ['add','sub','div','random_trace'])
        for changed in [output.replace('Quot.sound','sorryAx'),
                        output+'\nunexpected warning', output.splitlines()[0],
                        'unexpected warning\n'+output]:
            with self.subTest(output=changed), self.assertRaises(ValueError):
                arithmetic.audit(changed)

    def reject_mutation(self, name, offset, value):
        spec = json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
        extracted = {key:bytes.fromhex(unit['hex']) for key,unit in spec['units'].items()}
        data = bytearray(extracted[name])
        data[offset] = value
        extracted[name] = bytes(data)
        source = arithmetic.certificate(extracted,'deliberate synthetic mutation')
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'Mutant.lean'
            path.write_text(source)
            result = subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],
                                    cwd=ROOT,text=True,capture_output=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn(f'{name} = Doom19.{name}',result.stdout)
            self.assertIn('false',result.stdout)

    def test_division_guard_mutation_fails_kernel_certificate(self):
        self.reject_mutation('fixedDivBytes',26,0x7d)  # JGE instead of JL

    def test_rng_table_mutation_fails_kernel_certificate(self):
        self.reject_mutation('randomTableBytes',0,1)

    def test_add_substitution_fails_kernel_certificate(self):
        self.reject_mutation('addBytes',0,0x29)  # SUB instead of ADD

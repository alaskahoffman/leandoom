"""Proof certificates must reject altered original player-turn instructions."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_turn as turn


class OriginalTurnTests(unittest.TestCase):
    def check_certificate(self, raw):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'Turn.lean'
            path.write_text(turn.certificate(raw,'synthetic certificate regression'))
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],
                                  cwd=ROOT,capture_output=True,text=True)

    def test_kernel_certificate_and_axiom_audit(self):
        raw=bytes.fromhex(json.loads((ROOT/'tests/reference/original-turn.json').read_text())['hex'])
        result=self.check_certificate(raw)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        turn.audit(result.stdout)
        for changed in [result.stdout.replace('Quot.sound','sorryAx'),
                        result.stdout.splitlines()[0],result.stdout+'\nextra theorem']:
            with self.assertRaises(ValueError):turn.audit(changed)

    def test_changed_shift_and_write_address_fail_certificate(self):
        raw=bytes.fromhex(json.loads((ROOT/'tests/reference/original-turn.json').read_text())['hex'])
        for offset,value in [(13,15),(16,36)]:
            with self.subTest(offset=offset):
                mutated=bytearray(raw);mutated[offset]=value
                result=self.check_certificate(mutated)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('code = Doom19.playerTurnBytes',result.stdout)
                self.assertIn('is false',result.stdout)
                with self.assertRaises(ValueError):turn.audit(result.stdout)


if __name__=='__main__':unittest.main()

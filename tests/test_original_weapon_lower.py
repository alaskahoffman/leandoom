"""Byte-bound dead-player lowering proof, strict audit and negative certificates."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_lower as proof
class WeaponLowerTests(unittest.TestCase):
    def setUp(self):
        spec=json.loads((ROOT/'tests/reference/original-weapon-lower.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}
    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Check.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','bad._native.ax_1'),result.stdout+'unexpected',result.stdout.replace('live_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_mutated_width_increment_compare_branch_and_return_rejected(self):
        for offset in [0,1,5,10,13,18,21,22,26,29,59]:
            with self.subTest(offset=offset):
                code=bytearray(self.raw['lower']);code[offset]^=1
                result=self.lean(proof.certificate({'lower':bytes(code)},'test'))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('decide',result.stdout)
    def test_missing_contract_and_wrong_live_dead_branch_rejected(self):
        source=proof.certificate(self.raw,'test')
        for old,new in [('(h : Inputs s y)','(h : True)'),('lowerHeight y true','lowerHeight y false'),('s.regs 4+4','s.regs 4+8')]:
            with self.subTest(change=new):
                result=self.lean(source.replace(old,new))
                self.assertNotEqual(result.returncode,0)
    def test_lowering_and_wrapping_memory(self):
        result=self.lean((ROOT/'tests/reference/weapon-lower.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.split(),['true','true'])
    def test_halfword_decode_and_execution(self):
        result=self.lean((ROOT/'tests/reference/x86-lower-half.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.split(),['true'])
if __name__=='__main__':unittest.main()

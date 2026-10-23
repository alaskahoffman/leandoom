"""Original-byte armor certificate, adversarial checks and actual machine runs."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_armor as proof

class PlayerArmorTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-armor.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Armor.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.ax_1'),
                    result.stdout.replace('armor_checked','missing'),result.stdout+'extra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_mutated_original_bytes_rejected(self):
        bad=dict(self.raw); code=bytearray(bad['armorBytes'])
        # Change the original green-armor divisor from three to two.
        at=code.index(bytes.fromhex('bb03000000'));code[at+1]=2;bad['armorBytes']=bytes(code)
        result=self.lean(proof.certificate(bad,'test'))
        self.assertNotEqual(result.returncode,0)
        self.assertIn('decide',result.stdout)

    def test_missing_initial_encoding_rejected(self):
        source=proof.certificate(self.raw,'test')
        for name,premise in [('damage','(damage : s.regs 7 = d.toBitVec)'),
                             ('points','(points : armor s = v.armor.toBitVec)'),
                             ('armorType','(armorType : kind s = v.armorType.toBitVec)')]:
            with self.subTest(premise=name):
                bad=source.replace(premise,'').replace('exact correspondence s f v d damage points armorType',
                    'exact correspondence s f v d '+ ' '.join('(by assumption)' if n==name else n for n in ['damage','points','armorType']))
                result=self.lean(bad)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('error:',result.stdout)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_actual_machine_paths_and_division_faults(self):
        result=self.lean((ROOT/'tests/reference/player-armor.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(' '.join(result.stdout.split()),'['+', '.join(['true']*21)+']')

    def test_corpus_includes_quotient_depletion_boundaries(self):
        cases=set(proof.cases())
        for damage,divisor,kind in [(5,3,1),(10,3,1),(20,2,2),(-3,2,2)]:
            q=(abs(damage)//divisor)*(-1 if damage<0 else 1)
            for delta in [-1,0,1]:self.assertIn((damage,q+delta,kind),cases)
        self.assertIn((-2**31,-2**31,1),cases)

if __name__=='__main__':unittest.main()

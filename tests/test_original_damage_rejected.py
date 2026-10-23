"""Original nonlethal damage CALL/RET certificate, including rejected hits."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_damage_rejected as proof

class DamageRejectedTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-damage-return.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        arithmetic=json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
        self.raw['painState']=bytes.fromhex(self.spec['painState']['hex'])
        self.raw['table']=bytes.fromhex(arithmetic['units']['randomTableBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Entry.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_strict_axioms(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr);proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','fake._native.ax_1'),
                    result.stdout.replace('live_checked','missing'),result.stdout+'unreviewed']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_mutated_guards_stack_and_epilogue_rejected(self):
        for unit,at in [('entry',0),('entry',0x2a47f-0x2a460),('entry',0x2a5b6-0x2a460+2),
                        ('tail',104),('tail',107),('tail',108),('tail',109),('tail',110),('fiveCall',1)]:
            with self.subTest(unit=unit,offset=at):
                raw=dict(self.raw);code=bytearray(raw[unit]);code[at]^=1;raw[unit]=bytes(code)
                result=self.lean(proof.certificate(raw,'test'))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('decide',result.stdout)

    def test_missing_contract_and_wrong_live_skill_rejected(self):
        source=proof.certificate(self.raw,'test')
        self.assertNotIn('(applied :',source)
        for old,new in [('(h : Inputs s v d baby rngState.play)','(h : True)'),
                        ('(h : Inputs s v d baby rngState.play)','(h : DamageReturn.JoinedInputs s v d baby rngState.play)'),
                        ('(site : pc ∈ PlayerDamageEntry.sites)','(site : True)'),
                        ('PlayerDamage.apply v d none false baby rngState','PlayerDamage.apply v d none false (!baby) rngState'),
                        ('(alive : (Doom.PlayerDamage.apply v d none false baby rngState).killed = false)','(alive : True)')]:
            with self.subTest(change=new):
                self.assertIn(old,source)
                result=self.lean(source.replace(old,new))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('mismatch',result.stdout.lower())

    def test_continuous_machine_paths(self):
        result=self.lean((ROOT/'tests/reference/damage-rejected.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.split(),['true','true','true','true'])

    def test_every_rng_index_and_each_outcome_in_corpus(self):
        corpus=set(proof.previous.cases())
        for seed in range(256):
            for d,shoot in [(5,1),(100,1),(5,0)]:
                self.assertIn((d,100,0,0,shoot,0,0,0,100,0,seed),corpus)

if __name__=='__main__':unittest.main()

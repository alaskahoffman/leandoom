"""Original tactile/actor-health certificate and native paths."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_actor_health as proof

class ActorHealthTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-actor-health.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}

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

    def test_mutated_tactile_and_actor_instructions_rejected(self):
        for unit,at in [('actor',3),('actor',70),('actor',77),('actor',84),('tactile',0),('tactile',9),('tactileReturn',0),('tactileReturn',3)]:
            with self.subTest(unit=unit,offset=at):
                raw=dict(self.raw);code=bytearray(raw[unit]);code[at]^=1;raw[unit]=bytes(code)
                result=self.lean(proof.certificate(raw,'test'))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('decide',result.stdout)

    def test_wrong_entry_relation_site_and_live_skill_rejected(self):
        source=proof.certificate(self.raw,'test')
        for old,new in [('(h : JoinedInputs s v d baby)','(h : True)'),
                        ('(h : JoinedInputs s v d baby)','(h : PlayerHealth.Inputs s v d baby)'),
                        ('(site : pc ∈ PlayerDamageEntry.sites)','(site : True)'),
                        ('PlayerDamage.apply v d none false baby rng','PlayerDamage.apply v d none false (!baby) rng')]:
            with self.subTest(change=new):
                self.assertIn(old,source)
                result=self.lean(source.replace(old,new))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('mismatch',result.stdout.lower())

    def test_continuous_machine_paths(self):
        result=self.lean((ROOT/'tests/reference/actor-health.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.split(),['true','true','true','true'])

    def test_overflow_and_clamp_boundaries_in_corpus(self):
        corpus=set(proof.cases())
        for d in [-2**31,-1,0,1,99,100,101,2**31-1]:
            for hp in [-2**31,-1,0,1,99,100,101,2**31-1]:
                for count in [-2**31,-1,0,1,99,100,101,2**31-1]:
                    self.assertIn((d,100,0,0,1,0,0,0,hp,count),corpus)

if __name__=='__main__':unittest.main()

"""Whole-ledger recursion, admission bounds, and original-evaluator adequacy."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_accounting as proof
class NoiseAccountingTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('budget_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts(self):
        s=proof.certificate()
        for old,new in [('(shape : addresses xs=layout)','(shape : True)'),
            ('(rep : Represents generation s.memory xs)','(rep : True)'),
            ('(safe : SectorSafe layout s)','(safe : True)'),
            ('(h : CheckedTrace layout phase s t w n)','(h : True)'),
            ('(rep : Represents generation s.core.memory xs)','(rep : True)'),
            ('n≤2*layout.length','n≤layout.length'),
            ('(le : k≤j)','(le : True)'),
            ('(run : eval k phase s=some t)','(run : True)'),
            ('(pc : s.pc=phase.pc)','(pc : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_cyclic_traversal_whole_ledger_and_return(self):
        s=(ROOT/'tests/reference/original-noise-accounting.lean').read_text()
        s=s.replace('end Doom.Verification.NoiseAccountingFixture','''
example : E1M1NoiseRecursive.eval 9 .sector initial=some result :=
  E1M1NoiseTraceFuel.eval_mono 3 9 .sector initial result (by decide) evaluated
example : ∃ k, E1M1NoiseRecursive.Runs (E1M1NoiseRecursive.bound k) initial result := checked.execution rfl
end Doom.Verification.NoiseAccountingFixture''')
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_wrong_admissions_marks_and_insufficient_fuel_rejected(self):
        s=(ROOT/'tests/reference/original-noise-accounting.lean').read_text().split('theorem initial_safe')[0]
        claims=['charge initial.core=0','charge called.core=1',
            'Represents (7#32) result.core.memory [(origin,.blocked),(other,.unseen)]',
            '(E1M1NoiseRecursive.eval 2 .sector initial).isSome=true']
        for claim in claims:
            with self.subTest(claim=claim):
                r=self.lean(s+'example : '+claim+' := by decide +kernel\nend Doom.Verification.NoiseAccountingFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
    def test_aliasing_and_bad_count_cannot_satisfy_guards(self):
        s=(ROOT/'tests/reference/original-noise-accounting.lean').read_text().split('theorem initial_safe')[0]
        for regs in ['write initial.core.regs 4 (0x13584#32)','write initial.core.regs 2 (2#32)']:
            with self.subTest(regs=regs):
                r=self.lean(s+'example : E1M1NoiseLedger.SectorSafe layout { initial.core with regs := '+regs+' } := by\n  constructor <;> decide +kernel\nend Doom.Verification.NoiseAccountingFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
if __name__=='__main__':unittest.main()

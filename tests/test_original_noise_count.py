"""Exact count transfer, first/second blockers and recursive parent restoration."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_count as proof
class NoiseCountTests(unittest.TestCase):
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
        for old,new in [('(safe : E1M1NoiseOpeningFrame.CallerSafe s)','(safe : True)'),
            ('(allocation : Allocation table stack)','(allocation : True)'),
            ('(child : CheckedTrace (layout table) .sector (dispatch s) u w n)','(child : True)'),
            ('(reserve : Reserve stack .lines n s)','(reserve : True)'),
            ('(call : (dispatch s).pc=0x26f60)','(call : True)'),
            ('(entry : Entry phase s)','(entry : True)'),
            ('(trace : CheckedTrace (layout table) phase s t w n)','(trace : True)'),
            ('(reserve : Reserve stack phase n s)','(reserve : True)'),
            ('56*table.length+20','28*table.length+20')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def fixture(self):
        return (ROOT/'tests/reference/original-noise-count.lean').read_text()
    def test_recursive_first_blocker_parent_restoration_and_all_entries(self):
        r=self.lean(self.fixture());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_bad_count_and_false_restoration_rejected(self):
        prefix=self.fixture().split('theorem allocated')[0]+"open E1M1NoiseCount\ndef after := advance childEnd\ndef calledAgain := dispatch after\n"
        cases=[(prefix.replace('if r=2 then 0','if r=2 then 2'),
                'Legal (initial.core.regs 2)', 'unfold Legal; decide +kernel'),
            (prefix,'after.core.regs 1=1','decide +kernel'),
            (prefix,'calledAgain.core.regs 2=0','decide +kernel'),
            (prefix+'def secondBlock : X86Memory.State := { parent.core with regs := write parent.core.regs 1 1 }\n',
                '(E1M1NoiseIteration.dispatched secondBlock).pc=0x26f60','decide +kernel')]
        for source,claim,tactic in cases:
            with self.subTest(claim=claim):
                r=self.lean(source+f'example : {claim} := by {tactic}\nend Doom.Verification.NoiseCountFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('false',r.stdout)
    def test_plain_line_recursive_count_one(self):
        s=self.fixture().split('open E1M1NoiseCount\n')[0]
        s=s.replace('(wall+16,68)','(wall+16,4)').replace('⟨wall,68,0,1,origin,origin⟩','⟨wall,4,0,1,origin,origin⟩').replace('if r=2 then 0','if r=2 then 1')
        s+='''open E1M1NoiseCount
example : Every Entry checked.trace := all_entries allocated checked entry_reserve (by unfold Entry Legal; decide +kernel)
example : called.core.regs 2=1 ∧ after.core.regs 1=1 ∧ calledAgain.core.regs 2=1 := by decide +kernel
end Doom.Verification.NoiseCountFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

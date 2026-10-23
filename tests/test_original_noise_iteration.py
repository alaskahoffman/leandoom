"""Joined sound iteration/sector contracts and concrete repeated-line witnesses."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_iteration as proof
class NoiseIterationTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('sector_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_iteration_loop_and_completion_contracts(self):
        s=proof.certificate()
        for old,new in [('(h : E1M1NoiseIteration.Inputs s)','(h : True)'),
            ('(h : E1M1NoiseIteration.LoopInputs k s)','(h : True)'),
            ('(nonempty : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6)','(nonempty : True)'),
            ('(inputs : E1M1NoiseIteration.LoopInputs k (E1M1NoiseIteration.started s))','(inputs : True)'),
            ('(done : (E1M1NoiseIteration.loop k (E1M1NoiseIteration.started s)).pc=0x27011)','(done : True)'),
            ('n≤95 ∧','n≤94 ∧'),('n≤95*k+32','n≤95*k+31')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_repeated_lines_and_real_returns(self):
        s=(ROOT/'tests/reference/original-noise-iteration.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_wrong_observations_rejected(self):
        # Reuse concrete state definitions; avoid rechecking unrelated witnesses
        # for each deliberately false observation.
        definitions=(ROOT/'tests/reference/original-noise-iteration.lean').read_text().split('theorem inputs_zero')[0]
        for claim in ['(after 4 0).pc=0x27011',
            'load32 (after 3 0).core.memory (child+18)=1',
            'load32 (after 4 0).core.memory (child+18)=2',
            '(E1M1NoiseIteration.sectorResult 5 (initial 0)).core.regs 4=1']:
            with self.subTest(claim=claim):
                r=self.lean(definitions+'example : '+claim+' := by decide\nend Doom.Verification.NoiseIterationFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
    def test_progress_requires_parent_frame(self):
        s='''import Doom.Proofs.E1M1NoiseIteration
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
example (s : X86Memory.State)
    (index : (E1M1NoiseIteration.resumed s).core.regs 6=s.regs 6)
    (offset : (E1M1NoiseIteration.resumed s).core.regs 5=s.regs 5) :
    (E1M1NoiseIteration.result s).core.regs 6=s.regs 6+1 ∧
    (E1M1NoiseIteration.result s).core.regs 5=s.regs 5+4 :=
  E1M1NoiseIteration.progress s index offset
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for field in ['index','offset']:
            reg=6 if field=='index' else 5
            old=f'({field} : (E1M1NoiseIteration.resumed s).core.regs {reg}=s.regs {reg})'
            self.assertIn(old,s)
            r=self.lean(s.replace(old,f'({field} : True)'));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

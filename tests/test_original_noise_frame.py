"""Kernel frame/progress proofs, missing-premise rejection and alias witnesses."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_frame as proof
class NoiseFrameTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('child_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts_and_bounds(self):
        s=proof.certificate()
        for old,new in [('(h : Saved entry s)','(h : True)'),
            ('(sp : t.regs 4=s.regs 4)','(sp : True)'),
            ('(frame : PlayerHeight.Frame s.memory t.memory writes)','(frame : True)'),
            ('(safe : ∀ a, a ∈ slots entry → ∀ b, b ∈ writes → Apart a b)','(safe : True)'),
            ('(safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core)','(safe : True)'),
            ('(terminal : (E1M1NoiseAlert.sectorResult (NoiseTraversal.recursiveCall parent f).core).pc=0x27011)','(terminal : True)'),
            ('E1M1NoiseRecursive.Runs 36','E1M1NoiseRecursive.Runs 35'),
            ('(index : (s.regs 6).toNat<n)','(index : True)'),
            ('(small : n≤2147483647)','(small : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_wrapping_fresh_pruned_and_alias_witnesses(self):
        r=self.lean((ROOT/'tests/reference/original-noise-frame.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_bad_observations_rejected(self):
        definitions=(ROOT/'tests/reference/original-noise-frame.lean').read_text().split('theorem safe')[0]
        for claim in ['(NoiseTraversal.returned (boundary 1 false).core).pc=0x27007',
            '(NoiseTraversal.returned (boundary 2 true).core).core.regs 4=0xfffffff9',
            '(NoiseTraversal.advanced (NoiseTraversal.returned (boundary 0 false).core).core).core.regs 6=7',
            'Apart (1#32) (2#32)']:
            with self.subTest(claim=claim):
                tactic='unfold Apart; decide' if claim.startswith('Apart') else 'decide'
                r=self.lean(definitions+'example : '+claim+' := by '+tactic+'\nend Doom.Verification.NoiseFrameFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
    def test_wrap_breaks_unrestricted_progress(self):
        r=self.lean('''import Doom.Proofs.E1M1NoiseFrame
open Doom Doom.Proofs Doom.Verification X86 X86Memory
-- If the index is allowed to wrap, the claimed decreasing measure is false.
def s : X86Memory.State := ⟨fun _ => 0xffffffff,fun _ => 0⟩
example : ¬(4294967296-((NoiseTraversal.advanced s).core.regs 6).toNat <
    4294967296-(s.regs 6).toNat) := by decide
''')
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

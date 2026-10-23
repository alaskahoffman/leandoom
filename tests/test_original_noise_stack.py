"""Derive recursive memory guards from one admission-bounded stack reserve."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_stack as proof
class NoiseStackTests(unittest.TestCase):
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
        for old,new in [('(allocation : Allocation table stack)','(allocation : True)'),
            ('(reserve : Reserve stack phase n s)','(reserve : True)'),
            ('(trace : CheckedTrace (layout table) phase s t w n)','(trace : True)'),
            ('(ledger : Represents generation s.core.memory xs)','(ledger : True)'),
            ('(shape : addresses xs=layout table)','(shape : True)'),
            ('(high : (s.core.regs 4).toNat+4 ≤ stack.hi)','(high : True)'),
            ('(bound : stack.hi≤2^32)','(bound : True)'),
            ('(bounds : Bounded table limit)','(bounds : True)'),
            ('(map : MapRep table s.core.memory)','(map : True)'),
            ('56*table.length+20','28*table.length+20'),
            ('2*table.length*(limit+1)+1','table.length*(limit+1)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_full_cycle_child_resume_skip_paths_and_automatic_budget(self):
        r=self.lean((ROOT/'tests/reference/original-noise-stack.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def prefix(self):
        return '''import Doom.Proofs.E1M1NoiseStack
open Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoiseStack
set_option backward.isDefEq.respectTransparency false
def st (sp : Word) : X86Control.State := ⟨⟨fun _ => sp, fun _ => 0⟩,none,0x26f60⟩
'''
    def test_exact_stack_boundaries(self):
        s=self.prefix()+'''
example : Reserve ⟨100,152⟩ .sector 1 (st 148) := by unfold Reserve need; decide +kernel
example : Reserve ⟨100,180⟩ .sector 2 (st 176) := by unfold Reserve need; decide +kernel
example : Reserve ⟨100,128⟩ .lines 0 (st 124) := by unfold Reserve need; decide +kernel
example : Reserve ⟨4294967244,4294967296⟩ .sector 1 (st 4294967292) := by unfold Reserve need; decide +kernel
example : Reserve ⟨100,152⟩ .lines 0 (Doom.Proofs.E1M1NoisePreservation.startLines (st 148)) :=
  Reserve.start (show Reserve ⟨100,152⟩ .sector 1 (st 148) from by unfold Reserve need; decide +kernel)
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_insufficient_space_and_wrapping_arena_rejected(self):
        for claim in [
            'Reserve ⟨100,152⟩ .sector 1 (st 147)',
            'Reserve ⟨100,180⟩ .sector 2 (st 175)',
            'Reserve ⟨100,128⟩ .lines 0 (st 123)',
            'Reserve ⟨100,151⟩ .sector 1 (st 148)',
            'Reserve ⟨4294967244,4294967297⟩ .sector 1 (st 4294967292)',
        ]:
            with self.subTest(claim=claim):
                r=self.lean(self.prefix()+'example : '+claim+' := by unfold Reserve need; decide +kernel\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
if __name__=='__main__':unittest.main()

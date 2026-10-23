"""Universal recursive frame certificates and concrete nested/alias witnesses."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_preservation as proof
class NoisePreservationTests(unittest.TestCase):
    def lean(self,s,timeout=180):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=timeout)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('restore_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_completion_separation_and_progress_contracts_required(self):
        s=proof.certificate()
        for old,new in [('(run : eval k phase s=some t)','(run : True)'),
            ('(run : eval k .sector s=some t)','(run : True)'),
            ('(safe : SectorSafe s.core (writes k .sector s))','(safe : True)'),
            ('(run : eval k .sector (NoiseTraversal.recursiveCall parent f)=some t)','(run : True)'),
            ('(safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core\n      (writes k .sector (NoiseTraversal.recursiveCall parent f)))','(safe : True)'),
            ('Runs (bound k+5)','Runs (bound k+4)'),
            ('(index : (parent.regs 6).toNat<n)','(index : True)'),
            ('(small : n≤2147483647)','(small : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_nested_cycle_restoration(self):
        r=self.lean((ROOT/'tests/reference/original-noise-preservation.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_omitting_writes_invalidates_universal_frame(self):
        s=(ROOT/'Doom/Proofs/E1M1NoiseFootprint.lean').read_text()
        # Only change the declared footprint, leaving instruction summaries intact.
        before,after=s.split('/-- Compose footprint guarantees',1)
        for field in ['s.regs 0+(66#32),','s.regs 4,','0x2c034,','0x2c030,','0x2c02c,',',0x2c038']:
            with self.subTest(omitted=field):
                self.assertIn(field,before)
                r=self.lean(before.replace(field,'',1)+'/-- Compose footprint guarantees'+after)
                self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_overlap_is_rejected_and_still_executes(self):
        definitions=(ROOT/'tests/reference/original-noise-frame.lean').read_text().split('theorem safe')[0]
        definitions=definitions.replace('import Doom.Proofs.E1M1NoiseFrame','import Doom.Proofs.E1M1NoisePreservation')
        s=definitions+'''
open E1M1NoisePreservation
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance
local instance (s : X86Memory.State) (w : List Word) : Decidable (SafeWords s w) := by
  letI (a : Word) : Decidable (∀ b, b ∈ w → Apart a b) := List.decidableBAll (Apart a) w
  exact List.decidableBAll (fun a => ∀ b, b ∈ w → Apart a b) (E1M1NoiseFrame.slots s)
local instance (s : X86Memory.State) (w : List Word) : Decidable (E1M1NoisePreservation.SectorSafe s w) := by
  unfold E1M1NoisePreservation.SectorSafe; infer_instance
def bad := NoiseTraversal.recursiveCall (parentAt 0x60011b false) none
example : (E1M1NoiseRecursive.eval 1 .sector bad).isSome=true := by decide
example : ¬E1M1NoisePreservation.SectorSafe bad.core (writes 1 .sector bad) := by decide
-- Removing only the five leading prologue writes must retain the later alias.
example : (bad.core.regs 4-(4#32)) ∈ (writes 1 .sector bad).drop 5 := by decide
end Doom.Verification.NoiseFrameFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

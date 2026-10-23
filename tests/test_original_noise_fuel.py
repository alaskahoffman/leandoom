"""Original-machine loop progress, guarded fuel bounds and contract rejection."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_fuel as proof
class NoiseFuelTests(unittest.TestCase):
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
        for old,new in [('(safe : DispatchSafe s)','(safe : True)'),
            ('(index : (s.core.regs 6).toNat<count s.core)','(index : True)'),
            ('(small : count s.core≤2147483647)','(small : True)'),
            ('(frame : E1M1NoisePreservation.SectorSafe (dispatch s).core w)','(frame : True)'),
            ('(safe : ∀ b, b ∈ E1M1NoiseFootprint.lineWrites s.core++w → BlockSummary.Apart (s.core.regs 3+(78#32)) b)','(safe : True)'),
            ('(loops : LoopGuards limit h)','(loops : True)'),
            ('(rep : Represents generation s.core.memory xs)','(rep : True)'),
            ('2*layout.length*(limit+1)+1','layout.length*(limit+1)'),
            ('(pc : s.pc=0x26f60)','(pc : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_cyclic_and_skipped_lines_signed_limit_and_bounded_execution(self):
        r=self.lean((ROOT/'tests/reference/original-noise-fuel.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_aliasing_actually_corrupts_dispatch_index(self):
        s=(ROOT/'tests/reference/original-noise-fuel.lean').read_text().split('theorem initial_safe')[0]
        s+='''
open E1M1NoiseLineProgress
def bad : X86Memory.State := { parent.core with regs := write parent.core.regs 4 (0x2c04c#32) }
example : ¬DispatchSafe bad := by unfold DispatchSafe; decide +kernel
example : (E1M1NoiseIteration.dispatched bad).core.regs 6≠bad.regs 6 := by decide +kernel
end Doom.Verification.NoiseFuelFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_exhausted_index_cannot_decrease(self):
        s='''import Doom.Proofs.E1M1NoiseLineProgress
open Doom Doom.Verification Doom.Proofs X86 X86Memory X86Control E1M1NoisePreservation E1M1NoiseLineProgress
def exhausted : X86Control.State := ⟨⟨fun _ => 0,fun _ => 0⟩,none,0x26fa8⟩
example : remaining (advance exhausted)+1=remaining exhausted := by decide +kernel
'''
        r=self.lean(s);self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
if __name__=='__main__':unittest.main()

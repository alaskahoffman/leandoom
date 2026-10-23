"""Recursive sound certificates, checked completion and real firing returns."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_recursive as proof
class NoiseRecursiveTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('fire_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_completion_entry_and_fire_contracts_required(self):
        s=proof.certificate()
        for old,new in [('(pc : s.pc=phase.pc)','(pc : True)'),
            ('(h : E1M1NoiseRecursive.eval k phase s=some t)','(h : True)'),
            ('(noise : E1M1NoiseRecursive.eval k .sector (NoiseAlert.result (E1M1NoiseAlert.noiseCall s).core)=some t)','(noise : True)'),
            ('(ret : t.pc=0x2d44f)','(ret : True)'),
            ('(attack : E1M1WeaponContinuation.AttackReturns s)','(attack : True)'),
            ('(enough : E1M1WeaponFire.Enough s)','(enough : True)'),
            ('121+E1M1NoiseRecursive.bound k','120+E1M1NoiseRecursive.bound k')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_nested_cycle_and_blocking_witnesses(self):
        s=(ROOT/'tests/reference/original-noise-recursive.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_wrong_results_and_exhaustion_rejected(self):
        definitions=(ROOT/'tests/reference/original-noise-recursive.lean').read_text().split('theorem complete')[0]
        for claim in ['(finalState false).pc=0x27006',
            'load32 (finalState false).core.memory (sector 2+18)=1',
            'load32 (finalState true).core.memory (sector 2+22)=0x600d01',
            '(E1M1NoiseRecursive.eval 3 .sector (initial false)).isSome=true']:
            with self.subTest(claim=claim):
                r=self.lean(definitions+'example : '+claim+' := by decide\nend Doom.Verification.NoiseRecursiveFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
    def test_all_supported_fire_witnesses(self):
        s=(ROOT/'tests/reference/original-weapon-continuation.lean').read_text().replace('import Doom.Proofs.E1M1WeaponContinuation','import Doom.Proofs.E1M1NoiseRecursive')
        s+='''\nnamespace Doom.Verification.WeaponContinuationFixture
open Doom.Proofs
private theorem noise_terminal (w : Fin 3) :
    (E1M1NoiseAlert.result (E1M1NoiseAlert.noiseCall (ready w.val)).core).pc=0x27011 := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide
private theorem noise_eval (w : Fin 3) :
    E1M1NoiseRecursive.eval 1 .sector (NoiseAlert.result (E1M1NoiseAlert.noiseCall (ready w.val)).core)=
      some (E1M1NoiseTraversal.noiseReturn (ready w.val)) := by
  have done := noise_terminal w
  change (E1M1NoiseAlert.sectorResult (NoiseAlert.result (E1M1NoiseAlert.noiseCall (ready w.val)).core).core).pc=0x27011 at done
  simp only [E1M1NoiseRecursive.eval,done,ite_true]
  rfl
private theorem noise_ret (w : Fin 3) : (E1M1NoiseTraversal.noiseReturn (ready w.val)).pc=0x2d44f := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide
example (w : Fin 3) : E1M1NoiseRecursive.Runs (121+E1M1NoiseRecursive.bound 1) ⟨ready w.val,none,0x2d410⟩
    (WeaponFire.returned (E1M1NoiseTraversal.noiseReturn (ready w.val)).core (E1M1NoiseTraversal.noiseReturn (ready w.val)).flags) :=
  E1M1NoiseRecursive.fire_execution _ _ _ _ (enough w) (actor_inputs w) (return_inputs w) (noise_eval w) (noise_ret w)
end Doom.Verification.WeaponContinuationFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

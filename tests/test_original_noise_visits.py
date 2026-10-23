"""Original sound mark/refinement proofs and finite-ledger revisit bounds."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_visits as proof
class NoiseVisitsTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('budget_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts_and_sharp_budget(self):
        s=proof.certificate()
        for old,new in [('(h : GateInputs s m b)','(h : True)'),
            ('(rep : Rep (load32 s.memory (0x13580#32)) (s.regs 0) s.memory m)','(rep : True)'),
            ('(count : s.regs 2=blocks b)','(count : True)'),
            ('(safe : PrologueSafe s)','(safe : True)'),
            ('(more : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6)','(more : True)'),
            ('(h : Admissions xs ys n)','(h : True)'),
            ('n≤2*xs.length','n≤xs.length'),
            ('(run : E1M1NoiseRecursive.eval k phase s=some t)','(run : True)'),
            ('(safe : ∀ b, b ∈ E1M1NoisePreservation.writes k phase s → BlockSummary.Apart (0x13580#32) b)','(safe : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_gate_prologue_and_two_visit_witnesses(self):
        r=self.lean((ROOT/'tests/reference/original-noise-visits.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_wrong_admission_and_signed_results_rejected(self):
        s=(ROOT/'tests/reference/original-noise-visits.lean').read_text().split('theorem relation')[0]
        claims=['admits .blocked true=true','admits .clear false=true','rank .unseen=1',
            '(E1M1NoiseAlert.sectorResult (initial .blocked true true)).pc=0x26fa6',
            '(E1M1NoiseAlert.sectorResult (initial .blocked false true)).pc=0x27011']
        for claim in claims:
            with self.subTest(claim=claim):
                r=self.lean(s+'example : '+claim+' := by decide\nend Doom.Verification.NoiseVisitsFixture\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('proved that the proposition',r.stdout)
    def test_nested_traversal_preserves_generation_and_untouched_sector(self):
        s=(ROOT/'tests/reference/original-noise-recursive.lean').read_text().split('example : E1M1NoiseRecursive.Runs')[0]
        s=s.replace('import Doom.Proofs.E1M1NoiseRecursive','import Doom.Proofs.E1M1NoiseVisits')
        s+='''
open E1M1NoiseVisits BlockSummary
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance
def w := E1M1NoisePreservation.writes 10 .sector (initial false)
local instance (a : Word) : Decidable (∀ b, b ∈ w → Apart a b) := List.decidableBAll (Apart a) w
theorem protects (a : Word) (ha : a=(0x13580#32) ∨ a=(0x700143#32) ∨ a=(0x700113#32)) :
    ∀ b, b ∈ w → Apart a b := by
  rcases ha with rfl|rfl|rfl <;> decide +kernel
example : load32 (finalState false).core.memory (0x13580#32)=load32 (initial false).core.memory (0x13580#32) :=
  eval_preserves_generation 10 .sector _ _ (complete false) (protects _ (Or.inl rfl))
example : Rep (7#32) (0x700101#32) (finalState false).core.memory .unseen := by
  apply eval_preserves_mark 10 .sector (initial false) (finalState false) _ _ .unseen
    (by unfold Rep; decide +kernel) (complete false)
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  · exact protects _ (Or.inr (Or.inl rfl))
  · exact protects _ (Or.inr (Or.inr rfl))
end Doom.Verification.NoiseRecursiveFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

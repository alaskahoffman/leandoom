"""Executable-bound line guards, recursive call and return regressions."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_traversal as proof
class NoiseTraversalTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-noise-traversal.json').read_text())
        self.raw={k:bytes.fromhex(r['hex']) for k,r in self.spec['units'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('child_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_code_tampering_rejected(self):
        for offset in [11,18,28,39,75,84,92,105,115]:
            with self.subTest(offset=offset):
                raw=self.raw.copy();b=bytearray(raw['traversal']);b[offset]^=1;raw['traversal']=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_missing_child_contracts_and_bounds_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('(call : (NoiseTraversal.blockResult s).pc=0x26f60)','(call : True)'),
            ('(terminal : (E1M1NoiseAlert.sectorResult (NoiseTraversal.blockResult s).core).pc=0x27011)','(terminal : True)'),
            ('(ret : (E1M1NoiseTraversal.childReturn s).pc=0x27006)','(ret : True)'),
            ('[0x26f60,0x27006] 7','[0x26f60,0x27006] 6'),('n≤43','n≤42')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_and_fixups(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),self.raw)
        for field,value in [('relocations',[]),('file_offset','0x68fbb'),('code_offset','0x26fa7')]:
            spec=copy.deepcopy(self.spec);spec['units']['traversal'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_branch_witnesses_and_boundaries(self):
        s=(ROOT/'tests/reference/original-noise-traversal.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('core.regs 4=1 ∧','core.regs 4=5 ∧'),('(child+18)=2','(child+18)=1'),
            ('(child+22)=0x600901','(child+22)=0'),('(gap 0x80000000).pc=0x27006','(gap 0x80000000).pc=0x26fc4'),
            ('core.regs 6=0x80000000','core.regs 6=0x7fffffff')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_joined_fire_return_witnesses(self):
        s=(ROOT/'tests/reference/original-weapon-continuation.lean').read_text().replace('import Doom.Proofs.E1M1WeaponContinuation','import Doom.Proofs.E1M1NoiseTraversal')
        s+='''\nnamespace Doom.Verification.WeaponContinuationFixture
open Doom.Proofs
private theorem noise_terminal (w : Fin 3) :
    (E1M1NoiseAlert.result (E1M1NoiseAlert.noiseCall (ready w.val)).core).pc=0x27011 := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide
private theorem noise_ret (w : Fin 3) : (E1M1NoiseTraversal.noiseReturn (ready w.val)).pc=0x2d44f := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide
example (w : Fin 3) : ∃ n, n≤152 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseTraversal.program [] n
    ⟨ready w.val,none,0x2d410⟩ (E1M1NoiseTraversal.fireReturn (ready w.val)) :=
  E1M1NoiseTraversal.fire_return_execution _ _ (enough w) (actor_inputs w) (return_inputs w) (noise_terminal w) (noise_ret w)
end Doom.Verification.WeaponContinuationFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

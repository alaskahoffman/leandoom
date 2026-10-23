"""Executable-bound noise entry, revisit decision and sector-write regressions."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_alert as proof
class NoiseAlertTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-noise-alert.json').read_text())
        self.raw={k:bytes.fromhex(r['hex']) for k,r in self.spec['units'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('fire_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_code_tampering_rejected(self):
        for field,offset in [('entry',14),('entry',25),('sector',21),('sector',29),('sector',40),('sector',65)]:
            with self.subTest(field=field,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[field]);b[offset]^=1;raw[field]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_missing_fire_contracts_and_bounds_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('(enough : E1M1WeaponFire.Enough s)','(enough : True)'),
            ('(actor : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)','(actor : True)'),
            ('(attack : E1M1WeaponContinuation.AttackReturns s)','(attack : True)'),('[0x26f60] 8','[0x26f60] 7'),('n≤141','n≤140')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_and_fixups(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),self.raw)
        for name in ['entry','sector']:
            spec=copy.deepcopy(self.spec);spec['units'][name]['relocations']=[]
            with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_branch_witnesses_and_boundaries(self):
        s=(ROOT/'tests/reference/original-noise-alert.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('(sector+18)=1','(sector+18)=2'),('core.regs 4=0xffffffe9','core.regs 4=0xfffffff1'),
            ('(sector+22)=0x600801','(sector+22)=0'),('memory 0x13580=0','memory 0x13580=1'),
            ('(NoiseAlert.result alias).core.regs 0=0x600801','(NoiseAlert.result alias).core.regs 0=sector')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_joined_fire_witnesses(self):
        # Reuse the existing actual actor/psprite contracts for all three weapons.
        s=(ROOT/'tests/reference/original-weapon-continuation.lean').read_text().replace('import Doom.Proofs.E1M1WeaponContinuation','import Doom.Proofs.E1M1NoiseAlert')
        s+='''\nnamespace Doom.Verification.WeaponContinuationFixture
example (w : Fin 3) : ∃ n, n≤141 ∧ X86CodeMemory.Prefix Doom.Proofs.FloorCaller.cm Doom.Proofs.E1M1NoiseAlert.program [] n
    ⟨ready w.val,none,0x2d410⟩
      (Doom.Proofs.E1M1NoiseAlert.result (Doom.Proofs.E1M1NoiseAlert.noiseCall (ready w.val)).core) :=
  Doom.Proofs.E1M1NoiseAlert.fire_execution _ _ (enough w) (actor_inputs w) (return_inputs w)
end Doom.Verification.WeaponContinuationFixture
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

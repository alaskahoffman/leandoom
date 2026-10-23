"""Psprite machine-code certificates and adversarial boundary checks."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_psprite_step as proof

class PspriteStepTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-psprite-step.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec)
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            # These checks test theorem contracts. Keep the interpreter opaque so a
            # wrong fuel value fails directly instead of unfolding the full VM.
            first,rest=s.split('\n',1)
            s=first+'\nset_option backward.isDefEq.respectTransparency true\nattribute [local irreducible] Doom.Verification.X86Routine.run Doom.Verification.X86CodeMemory.run\n'+rest
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    def reject(self,pairs):
        s=proof.certificate(self.raw)
        for old,new in pairs:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new))
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout);self.assertNotIn('timeout',r.stdout.lower())
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('append_step','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_original_bytes(self):
        for offset in [0,20,26,31,34,47,49]:
            with self.subTest(offset=offset):
                raw=dict(self.raw);data=bytearray(raw['psprite']);data[offset]^=1;raw['psprite']=bytes(data)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_boundaries_budgets_and_contract(self):
        self.reject([('[0x2dc6f] 8','[0x2dc6f] 7'),
                     ('PspriteStep.exits 15','PspriteStep.exits 14'),
                     ('⟨s,f,0x2dc6f⟩','⟨s,f,0x2dc75⟩'),
                     ('cm E1M1PspriteStep.program [] n','cm E1M1PspriteStep.program [0x2d040] n'),
                     ('(selection : WeaponSelect.Inputs s buttons choice)','(selection : True)'),
                     ('(E1M1PspriteStep.result (WeaponSelect.result before.core buttons choice).core)' ,
                      '(E1M1PspriteStep.result s)')])
    def test_mapping_and_fixups(self):
        for key,value in [('file_offset','0x0'),('code_offset','0x2dc61'),('relocations',[dict(offset=0,object=3,target='0x0')])]:
            spec=copy.deepcopy(self.spec);spec['units']['psprite'][key]=value
            with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,spec)
    def test_actual_setter_call(self):
        r=self.lean('''import Doom.Proofs.E1M1PspriteStep
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
example : X86Routine.decodeAt PspriteStep.code 48=some (.call (-3157),5) := by decide
example (s : X86Memory.State) (present : PspriteStep.stateWord s≠0)
    (finite : PspriteStep.tics s≠0xffffffff) (expired : PspriteStep.tics s-1=0) :
    (PspriteStep.result s).pc=0x2d040 := (PspriteStep.dispatch_arguments s present finite expired).1
''');self.assertEqual(r.returncode,0,r.stdout+r.stderr)

if __name__=='__main__':unittest.main()

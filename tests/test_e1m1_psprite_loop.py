"""Psprite loop certificates, decoder boundary and adversarial contracts."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_psprite_loop as proof

class PspriteLoopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-psprite-loop.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec)
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            # Compare contracts directly instead of unfolding a mismatched VM.
            first,rest=s.split('\n',1)
            s=first+'\nset_option backward.isDefEq.respectTransparency true\nattribute [local irreducible] Doom.Verification.X86Routine.run Doom.Verification.X86CodeMemory.run Doom.Proofs.E1M1PspriteLoop.finished\n'+rest
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
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('append_loop','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_original_bytes(self):
        for offset in [0,3,6,8,12,18,24,30,33,38]:
            with self.subTest(offset=offset):
                raw=dict(self.raw);data=bytearray(raw['tail']);data[offset]^=1;raw['tail']=bytes(data)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_boundaries_budgets_and_contract(self):
        self.reject([('[0x2dc6f,0x2dc9e] 4','[0x2dc6f,0x2dc9e] 3'),
                     ('[] 6 ⟨s,f,0x2dcb6⟩','[] 5 ⟨s,f,0x2dcb6⟩'),
                     ('(weapon : s.core.regs 6=0)','(weapon : True)'),
                     ('(flashDone : (E1M1PspriteLoop.flash s).pc=0x2dc95)','(flashDone : True)'),
                     ('E1M1PspriteStep.program [] n s t','E1M1PspriteStep.program [] n s s'),
                     ('(E1M1PspriteLoop.finished t)','(E1M1PspriteLoop.finished s)')])
    def test_mapping_and_fixups(self):
        for key,value in [('file_offset','0x0'),('code_offset','0x2dc96'),('relocations',[dict(offset=0,object=3,target='0x0')])]:
            spec=copy.deepcopy(self.spec);spec['units']['tail'][key]=value
            with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,spec)
    def test_increment_decoder_and_flag_boundary(self):
        r=self.lean('''import Doom.Proofs.E1M1PspriteLoop
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
example : X86Routine.decodeAt [0x46] 0=some (.addImmediate 6 1,1) := by decide
example : X86Routine.decodeAt [0x40] 0=some (.addImmediate 0 1,1) := by decide
example : X86Routine.decodeAt [0x47] 0=none := by decide
example (s : X86Control.State) :
  (X86Routine.execute (.addImmediate 6 1) s).map (·.flags)=some none := rfl
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 3 (-47)) ⟨s,none,0x2dc9e⟩=none := rfl
example (s : X86Memory.State) (f : Option Flags) :
  (PspriteLoop.returned s f).pc=(load32 s.memory (s.regs 4+20)).toNat := (PspriteLoop.return_stack s f).1
''');self.assertEqual(r.returncode,0,r.stdout+r.stderr)

if __name__=='__main__':unittest.main()

"""Reject forged original setter bytes, call boundaries, and proof contracts."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_psprite_setter as proof

class PspriteSetterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-weapon-drop.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec)
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            first,rest=s.split('\n',1)
            s=first+'\nset_option backward.isDefEq.respectTransparency true\nattribute [local irreducible] Doom.Verification.X86Routine.run Doom.Verification.X86CodeMemory.run Doom.Proofs.E1M1PspriteSetter.slotResult Doom.Proofs.E1M1PspriteSetter.dispatched Doom.Proofs.E1M1PspriteSetter.resumed\n'+rest
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('slot_execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_original_bytes(self):
        for offset in [0,7,21,34,40,49,55,82,85,104,110]:
            with self.subTest(offset=offset):
                raw=dict(self.raw);data=bytearray(raw['setter']);data[offset]^=1;raw['setter']=bytes(data)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts(self):
        s=proof.certificate(self.raw)
        for old,new in [('[0x2d055,0x2d05e] 9','[0x2d055,0x2d05e] 8'),
                        ('(null : s.regs 3=0)','(null : True)'),
                        ('n ≤ 20','n ≤ 19'),('n ≤ 10','n ≤ 9'),('n ≤ 44','n ≤ 43'),
                        ('⟨s,f,0x2dc6f⟩','⟨s,f,0x2dc70⟩')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new))
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout);self.assertNotIn('timeout',r.stdout.lower())
    def test_mapping_and_relocations(self):
        for key,value in [('file_offset','0x0'),('code_offset','0x2d041'),('relocations',[])]:
            spec=copy.deepcopy(self.spec);spec['units']['setter'][key]=value
            with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,spec)
    def test_actual_call_and_return(self):
        s='''import Doom.Proofs.E1M1PspriteSetter
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
example (s : X86Memory.State) (f : Option Flags) :
  (PspriteSetter.called s f).pc=(load32 s.memory (s.regs 1+12)).toNat :=
  (PspriteSetter.call_contract s f).1
example (s : X86Memory.State) (f : Option Flags) :
  load32 (PspriteSetter.called s f).core.memory (s.regs 4-4)=0x2d095 :=
  (PspriteSetter.call_contract s f).2.2.2.2
example (s : X86Memory.State) (f : Option Flags) :
  (PspriteSetter.returned s f).pc=(load32 s.memory (s.regs 4+8)).toNat :=
  (PspriteSetter.return_contract s f).1
'''
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        r=self.lean(s.replace('=0x2d095','=0x2dc95'))
        self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)

if __name__=='__main__':unittest.main()

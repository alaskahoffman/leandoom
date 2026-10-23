"""Use-button branch certificates and adversarial contract checks."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_use_button as proof

class UseButtonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-use-button.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec)
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    def reject(self,pairs):
        s=proof.certificate(self.raw)
        for old,new in pairs:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new))
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('append_use','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_original_branch_call_and_latch_bytes(self):
        for offset in [3,5,13,18,26,35,47]:
            with self.subTest(offset=offset):
                raw=dict(self.raw);data=bytearray(raw['use']);data[offset]^=1;raw['use']=bytes(data)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_call_boundaries_and_budgets(self):
        self.reject([('UseButtonCode.exits 6','UseButtonCode.exits 5'),
                     ('⟨s,f,0x33476⟩','⟨s,f,0x3347a⟩'),
                     ('[0x2dc60] 4','[0x334a9] 4'),
                     ('⟨s,f,0x3348c⟩','⟨s,f,0x33496⟩')])
    def test_initial_contract_and_whole_chain_required(self):
        self.reject([('(selection : WeaponSelect.Inputs s buttons choice)','(selection : True)'),
                     ('UseButtonCode.exits 597','[0x334a9] 597'),
                     ('some (UseButtonCode.result (WeaponSelect.result before.core buttons choice).core)',
                      'some (UseButtonCode.result s)')])
    def test_original_mapping_and_fixups(self):
        for key,value in [('file_offset','0x0'),('code_offset','0x33477'),('relocations',[dict(offset=0,object=3,target='0x0')])]:
            s=copy.deepcopy(self.spec);s['units']['use'][key]=value
            with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,s)
    def test_real_calls_and_latch_edges(self):
        r=self.lean('''import Doom.Proofs.E1M1UseButton
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
example : UseButton.request false true=true := by decide
example : UseButton.request true true=false := by decide
example : UseButton.request true false=false := by decide
example : UseButton.request false false=false := by decide
example : X86Routine.decodeAt UseButtonCode.code 17=some (.call (-30588),5) := by decide
example : X86Routine.decodeAt UseButtonCode.code 46=some (.call (-22601),5) := by decide
example (s : X86Memory.State) :
  load32 (UseButtonCode.result s).core.memory ((UseButtonCode.result s).core.regs 4)=
    if UseButtonCode.requested s then 0x3348c else 0x334a9 := UseButtonCode.saved_return s
''');self.assertEqual(r.returncode,0,r.stdout+r.stderr)

if __name__=='__main__':unittest.main()

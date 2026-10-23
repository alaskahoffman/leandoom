"""Ready entry certificates, branch premises, and full raising-stack witness."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_ready_entry as proof
class WeaponReadyEntryTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-ready-entry.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['entry']['hex'])
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('raising_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_binary_rejected(self):
        for offset in [0,3,7,12,15,19,23,27,29,36,41,49,55,64]:
            with self.subTest(offset=offset):
                bs=bytearray(self.raw);bs[offset]^=1;r=self.lean(proof.certificate(bytes(bs)))
                self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('(h : WeaponReadyEntry.Inputs s frame w)','(h : True)'),
            ('(idlePose : frame.val≠154 ∧ frame.val≠155)','(idlePose : True)'),
            ('(low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared s))','(low : True)'),
            ('(a : WeaponReadyGate.attack (WeaponReadyEntry.prepared s)=0)','(a : True)'),
            ('(ready : (E1M1WeaponReady.raiseNext s).pc=0x2d2f0)','(ready : True)'),
            ('(ok : E1M1WeaponReady.raisedIdleReturn (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core)=some t)','(ok : True)'),
            ('n≤19','n≤18'),('n≤58','n≤57'),('n≤133','n≤132'),
            ('frame.val=154 ∨ frame.val=155','frame.val=154'),('⟨s,f,0x2d2f0⟩','⟨s,f,0x2d2fd⟩')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_relocations(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),{'entry':self.raw})
        for index in range(3):
            for field,value in [('object',2),('target','0x16b01'),('offset',0)]:
                spec=copy.deepcopy(self.spec);spec['units']['entry']['relocations'][index][field]=value
                with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_nonvacuous_entry_and_raising(self):
        s=(ROOT/'tests/reference/original-weapon-ready-entry.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('(initial 155 1 table)).pc=0x30ea0','(initial 155 1 table)).pc=0x2d333'),
            ('(initial 149 7 0x1617c)).pc=0x3f370','(initial 149 7 0x1617c)).pc=0x2d333'),
            ('final.core.regs 4=17','final.core.regs 4=13'),('final.pc=0x2dc95','final.pc=0x2dc96')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

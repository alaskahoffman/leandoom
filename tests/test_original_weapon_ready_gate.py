"""DOS ready decisions: certificates, live contracts, and nonvacuous branches."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_ready_gate as proof
class WeaponReadyGateTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-ready-gate.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['gate']['hex'])
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('live_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_binary_rejected(self):
        for offset in [3,5,9,29,34,46,47,59,63,68,86,94]:
            with self.subTest(offset=offset):
                bs=bytearray(self.raw);bs[offset]^=1;r=self.lean(proof.certificate(bytes(bs)))
                self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('(h : WeaponReadyGate.Inputs s w p hp a)','(h : True)'),
            ('(low : ¬WeaponReadyGate.lowering s)','(low : True)'),('(a : WeaponReadyGate.attack s=0)','(a : True)'),
            ('n≤16','n≤15'),('n≤39','n≤38'),('⟨s,f,0x2d333⟩','⟨s,f,0x2d339⟩'),
            ('| .fire => 0x2d410','| .fire => 0x2d392')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_relocations(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),{'gate':self.raw})
        for field,value in [('object',2),('target','0x12d99'),('offset',28)]:
            spec=copy.deepcopy(self.spec);spec['units']['gate']['relocations'][0][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_nonvacuous_branches(self):
        s=(ROOT/'tests/reference/original-weapon-ready-gate.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('(initial 10 0 1 7 1)).pc=0x2d040','(initial 10 0 1 7 1)).pc=0x2d410'),
            ('(initial 10 100 6 7 1)).pc=0x2d39c','(initial 10 100 6 7 1)).pc=0x2d410'),
            ('0xfffffffd=0x2d38d','0xfffffffd=0x2d35b')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

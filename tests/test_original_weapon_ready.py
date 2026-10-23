"""Original ready bobbing, real nested returns and proof-certificate rejection."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_ready as proof
class WeaponReadyTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-ready.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['idle']['hex'])
        self.raise_code=bytes.fromhex(json.loads((ROOT/'tests/reference/original-weapon-raise.json').read_text())['units']['raise']['hex'])
        self.setter=bytes.fromhex(json.loads((ROOT/'tests/reference/original-weapon-drop.json').read_text())['units']['setter']['hex'])
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def source(self):return proof.certificate(self.raw,self.raise_code,self.setter)
    def test_certificate_and_audit(self):
        r=self.lean(self.source());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('nested_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_binary_rejected(self):
        for field,offset in [('idle',0),('idle',12),('idle',20),('idle',39),('idle',50),('idle',59),('idle',84),('raise',57),('setter',84)]:
            with self.subTest(field=field,offset=offset):
                args={'idle':self.raw,'raise':self.raise_code,'setter':self.setter};bs=bytearray(args[field]);bs[offset]^=1;args[field]=bytes(bs)
                r=self.lean(proof.certificate(args['idle'],args['raise'],args['setter']));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts_rejected(self):
        s=self.source()
        for old,new in [('(h : WeaponReady.Inputs s bob time)','(h : True)'),
            ('(ok : E1M1WeaponReady.raisedIdleReturn s=some t)','(ok : True)'),
            ('(boundary : E1M1WeaponFlash.Boundary u.core p v)','(boundary : True)'),
            ('(pc : u.pc=0x2dc95)','(pc : True)'),('n ≤ 162','n ≤ 161'),('n ≤ 23','n ≤ 22'),('n ≤ 46','n ≤ 45'),('n ≤ 52','n ≤ 51'),
            ('s.regs 4+20','s.regs 4+16'),('⟨s,f,0x2d392⟩','⟨s,f,0x2d39c⟩'),
            ('(Weapon.readyIdle v bob time).weapon.x.raw.toBitVec','v.weapon.x.raw.toBitVec')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_relocations(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),{'idle':self.raw})
        for field,value in [('object',2),('target','0x2cf81'),('offset',11)]:
            spec=copy.deepcopy(self.spec);spec['units']['idle']['relocations'][0][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_nonvacuous_nested_stack(self):
        s=(ROOT/'tests/reference/original-weapon-ready.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('final.core.regs 4=61','final.core.regs 4=57'),('final.pc=0x2dc95','final.pc=0x2dc96')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)

if __name__=='__main__':unittest.main()

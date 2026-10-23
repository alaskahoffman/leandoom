"""Original A_Raise bytes, table data, live contracts and strict proof audit."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_raise as proof
class WeaponRaiseTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-raise.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.tables={k:bytes.fromhex(v['hex']) for k,v in self.spec['tables'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def source(self):return proof.certificate(self.raw,self.tables,self.spec)
    def test_certificate_and_audit(self):
        r=self.lean(self.source());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('dispatch_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_changed_instructions_and_tables_rejected(self):
        for offset in [0,9,22,27,46,57,63]:
            with self.subTest(byte=offset):
                raw=dict(self.raw);bs=bytearray(raw['raise']);bs[offset]^=1;raw['raise']=bytes(bs)
                r=self.lean(proof.certificate(raw,self.tables,self.spec));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
        for name in self.tables:
            with self.subTest(table=name):
                tables=dict(self.tables);bs=bytearray(tables[name]);bs[0]^=1;tables[name]=bytes(bs)
                r=self.lean(proof.certificate(self.raw,tables,self.spec));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts_rejected(self):
        s=self.source()
        for old,new in [('(h : Inputs s w y)','(h : True)'),
            ('(ready : (Weapon.raiseStep y).2=true)','(ready : True)'),
            ('n ≤ 17','n ≤ 16'),('s.regs 4-(12#32)','s.regs 4-(8#32)'),
            ('(Weapon.raiseStep y).1.raw.toBitVec','y.raw.toBitVec'),('(0x2d50d#32)','(0x2d50e#32)')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_relocations(self):
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(proof.table_data(binary,profile,self.spec),self.tables)
        for field,value in [('object',2),('target','0x12d9d'),('offset',45)]:
            spec=copy.deepcopy(self.spec);spec['units']['raise']['relocations'][0][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,spec)
    def test_nonvacuous_contracts_and_boundaries(self):
        s=(ROOT/'tests/reference/original-weapon-raise.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('initial 5','initial 0x60020d'),('0x260000','0x260001')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
if __name__=='__main__':unittest.main()

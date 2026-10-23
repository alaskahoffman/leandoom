"""Original light bytes, relocated flash tables, callback seams and live cases."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_psprite_light as proof

class PspriteLightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-psprite-light.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec);cls.tables=proof.table_data(cls.binary,cls.exe,cls.spec)
    def lean(self,s,contracts=False):
        with tempfile.TemporaryDirectory() as d:
            if contracts:
                first,rest=s.split('\n',1)
                s=first+'\nset_option backward.isDefEq.respectTransparency true\nattribute [local irreducible] Doom.Proofs.E1M1PspriteLight.advance Doom.Proofs.E1M1PspriteLight.chain Doom.Proofs.E1M1PspriteLight.suffix Doom.Proofs.PspriteChainDriver.chain\n'+rest
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.tables,self.spec),True);self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('live_actions','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_bytes_and_tables(self):
        for name in self.raw:
            for offset in [2,6,10]:
                with self.subTest(unit=name,offset=offset):
                    raw=dict(self.raw);bs=bytearray(raw[name]);bs[offset]^=1;raw[name]=bytes(bs)
                    r=self.lean(proof.certificate(raw,self.tables,self.spec));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
        for name in self.tables:
            with self.subTest(table=name):
                tables=dict(self.tables);bs=bytearray(tables[name]);bs[12]^=16;tables[name]=bytes(bs)
                r=self.lean(proof.certificate(self.raw,tables,self.spec));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_mapping_and_fixups(self):
        spec=copy.deepcopy(self.spec);spec['units']['light0']['code_offset']='0x2db41'
        with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,spec)
        for name in self.spec['tables']:
            spec=copy.deepcopy(self.spec);spec['tables'][name]['relocations']=[]
            with self.assertRaises(ValueError):proof.table_data(self.binary,self.exe,spec)
    def test_contracts(self):
        s=proof.certificate(self.raw,self.tables,self.spec)
        for old,new in [('[] 2 ⟨s,f,PspriteLight.entry i⟩','[] 1 ⟨s,f,PspriteLight.entry i⟩'),
                        ('(ok : E1M1PspriteLight.advance s=some t)','(ok : True)'),
                        ('n ≤ 32 ∧','n ≤ 31 ∧'),('32*fuel+46','32*fuel+45'),
                        ('(pc : s.pc=0x2dc95)','(pc : True)'),('(weaponIndex : s.core.regs 6=(0#32))','(weaponIndex : True)')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new),True)
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout);self.assertNotIn('timeout',r.stdout.lower())
    def test_real_flash_paths_and_rejections(self):
        s=(ROOT/'tests/reference/e1m1-psprite-light.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('0x603004,2,0x15d8c,3','0x603004,1,0x15d8c,3'),
                        ('0x603004,0,0,0','0x603004,1,0,0'),
                        ('6 (0x603000-236))).isNone=true','6 (0x603000-236))).isNone=false')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)

if __name__=='__main__':unittest.main()

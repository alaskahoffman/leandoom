"""DOS ammo acceptance, attack pose/state joins, and rejection checks."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_fire as proof
class WeaponFireTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-fire.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.data={k:bytes.fromhex(v['hex']) for k,v in self.spec['data'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.data));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('machine_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_bytes_and_data_rejected(self):
        for field,offset in [('entry',0),('entry',29),('decision',29),('decision',40),('fire',10),('fire',15),('fire',49),('pose',8),('pose',16),('weapons',0),('weapons',40)]:
            with self.subTest(field=field,offset=offset):
                raw=self.raw.copy();data=self.data.copy();dest=raw if field in raw else data;b=bytearray(dest[field]);b[offset]^=1;dest[field]=bytes(b)
                r=self.lean(proof.certificate(raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts_and_bounds_rejected(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(h : WeaponAmmo.Inputs s w ammo)','(h : True)'),
            ('(h : E1M1WeaponFire.Enough s)','(h : True)'),
            ('(setter : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)','(setter : True)'),
            ('(fire : (WeaponReadyGate.result s).pc=0x2d410)','(fire : True)'),
            ('n≤25','n≤24'),('n≤66','n≤65'),('n≤111','n≤110'),('⟨s,f,0x2d410⟩','⟨s,f,0x2d415⟩')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_original_extraction(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),self.raw)
        self.assertEqual(proof.table_data(binary,p,self.spec),self.data)
        for name in ['pose','weapons']:
            for field,value in [('offset','0x16a74'),('hex','00'*len(self.data[name]))]:
                spec=copy.deepcopy(self.spec);spec['data'][name][field]=value
                with self.assertRaises(ValueError):proof.table_data(binary,p,spec)
        spec=copy.deepcopy(self.spec);spec['units']['fire']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_nonvacuous_attack_and_signed_ammo(self):
        s=(ROOT/'tests/reference/original-weapon-fire.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('(0x16b00,12,28,4)','(0x16b00,11,28,4)'),('attack.core.regs 3=13','attack.core.regs 3=21'),
            ('attack.core.regs 4=0xfffffff1','attack.core.regs 4=0xfffffff5'),('installed.pc=0x2d09a','installed.pc=0x2d095')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

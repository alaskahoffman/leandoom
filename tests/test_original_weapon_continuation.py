"""Executable-bound fallback and attack-return correspondence regressions."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_continuation as proof
class WeaponContinuationTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-continuation.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['fallback']['hex'])
        self.states={r['index']:bytes.fromhex(r['hex']) for r in self.spec['states']}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.states));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('machine_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_code_and_states_rejected(self):
        for field,offset in [('code',0),('code',13),('code',123),('code',270),(5,8),(13,12),(21,8),(21,16)]:
            with self.subTest(field=field,offset=offset):
                raw=self.raw;states=self.states.copy();b=bytearray(raw if field=='code' else states[field]);b[offset]^=1
                if field=='code':raw=bytes(b)
                else:states[field]=bytes(b)
                r=self.lean(proof.certificate(raw,states));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_missing_contracts_and_wrong_bounds_rejected(self):
        s=proof.certificate(self.raw,self.states)
        for old,new in [('(h : WeaponFallback.Inventory s)','(h : True)'),
            ('(h : WeaponFallback.Inputs s own sh bu)','(h : True)'),
            ('(empty : ¬E1M1WeaponFire.Enough s)','(empty : True)'),
            ('(ret : E1M1WeaponContinuation.AttackReturns s)','(ret : True)'),
            ('(ret : (WeaponFallback.returned s).pc=0x2d41a)','(ret : True)'),
            ('n≤32','n≤31'),('n≤62','n≤61'),('n≤109','n≤108'),('n≤12','n≤11')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_mapping_and_fixups(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec)['fallback'],self.raw)
        self.assertEqual(proof.table_data(binary,p,self.spec),self.states)
        for field,value in [('index',6),('offset','0x15ab5'),('hex','00'*28)]:
            spec=copy.deepcopy(self.spec);spec['states'][0][field]=value
            with self.assertRaises(ValueError):proof.table_data(binary,p,spec)
        spec=copy.deepcopy(self.spec);spec['units']['fallback']['relocations']=[]
        with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_nonvacuous_witnesses_and_negative_ammo_boundary(self):
        s=(ROOT/'tests/reference/original-weapon-continuation.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('(p+248)=3','(p+248)=4'),('core.regs 4=0xfffffff5','core.regs 4=0xfffffff1'),
            ('core 116=2','core 116=1'),('core.regs 3=11','core.regs 3=19'),('rejected.core.regs 4=37','rejected.core.regs 4=33')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

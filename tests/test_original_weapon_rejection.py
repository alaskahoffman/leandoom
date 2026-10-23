"""Joined original rejected-shot execution, including the actual callback."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_rejection as proof
class WeaponRejectionTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-rejection.json').read_text())
        self.lower=json.loads((ROOT/'tests/reference/original-weapon-lower.json').read_text())
        self.raw=bytes.fromhex(self.lower['units']['lower']['hex'])
        self.states={r['index']:bytes.fromhex(r['hex']) for r in self.spec['states']}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.states));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('joined_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_code_and_state_tampering_rejected(self):
        for field,offset in [('code',5),('code',14),('code',59),(3,8),(11,12),(19,16)]:
            with self.subTest(field=field,offset=offset):
                raw=self.raw;states=self.states.copy();b=bytearray(raw if field=='code' else states[field]);b[offset]^=1
                if field=='code':raw=bytes(b)
                else:states[field]=bytes(b)
                r=self.lean(proof.certificate(raw,states));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_missing_contracts_and_wrong_bounds_rejected(self):
        s=proof.certificate(self.raw,self.states)
        for old,new in [('(low : WeaponLower.below s)','(low : True)'),
            ('(ret : load32 (WeaponLower.advancedMemory s) (s.regs 4)=0x2d095)','(ret : True)'),
            ('(empty : ¬E1M1WeaponFire.Enough s)','(empty : True)'),
            ('(inventory : WeaponFallback.Inventory (E1M1WeaponFire.afterCheck s).core)','(inventory : True)'),
            ('(lower : E1M1WeaponRejection.LowerReturns (E1M1WeaponRejection.fallback s).core t)','(lower : True)'),
            ('(setterPC : t.pc=0x2d2aa)','(setterPC : True)'),
            ('(ammoPC : (WeaponFallback.returned t.core).pc=0x2d41a)','(ammoPC : True)'),
            ('[0x2d095] 6','[0x2d095] 5'),('n≤122','n≤121')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_and_action_relocations(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.lower)['lower'],self.raw)
        self.assertEqual(proof.table_data(binary,p,self.spec),self.states)
        for field,value in [('index',4),('offset','0x15a7d'),('hex','00'*28),('relocations',[]),
            ('relocations',[dict(offset=12,object=2,target='0x2d490')]),('relocations',[dict(offset=12,object=1,target='0x2d491')])]:
            spec=copy.deepcopy(self.spec);spec['states'][0][field]=value
            with self.assertRaises(ValueError):proof.table_data(binary,p,spec)
    def test_live_witnesses_and_boundaries(self):
        s=(ROOT/'tests/reference/original-weapon-rejection.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('core.regs 4=5','core.regs 4=1'),('(p+116)=2','(p+116)=1'),('(p+256)=0x260000','(p+256)=0x200000'),
            ('¬WeaponLower.below (heightState 0x7a0000)','WeaponLower.below (heightState 0x7a0000)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

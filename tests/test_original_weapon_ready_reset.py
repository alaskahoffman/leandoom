"""Real pose reset, arbitrary actor returns, and certificate rejection."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_weapon_ready_reset as proof
class WeaponReadyResetTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-weapon-ready-reset.json').read_text())
        self.state=bytes.fromhex(self.spec['state']['hex'])
        self.raw=bytes.fromhex(json.loads((ROOT/'tests/reference/original-player-animation.json').read_text())['units']['setMobjStateBytes']['hex'])
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.state));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('machine_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_bytes_rejected(self):
        for field,offset in [('setter',0),('setter',32),('setter',38),('setter',60),('setter',90),('state',0),('state',4),('state',8),('state',12),('state',16)]:
            with self.subTest(field=field,offset=offset):
                data={'setter':self.raw,'state':self.state};b=bytearray(data[field]);b[offset]^=1;data[field]=bytes(b)
                r=self.lean(proof.certificate(data['setter'],data['state']));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_contracts_rejected(self):
        s=proof.certificate(self.raw,self.state)
        for old,new in [('(h : DeathSetter.SetterInputs p s ret)','(h : DeathSetter.SetterInputs p s)'),
            ('(reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s))','(reset : True)'),
            ('(h : DeathSetter.SetterInputs E1M1WeaponReadyReset.entry (E1M1WeaponReadyReset.call s).core 0x2d319)','(h : True)'),
            ('(weapon : WeaponReadyEntry.weapon (E1M1WeaponReadyReset.call s).core=BitVec.ofNat 32 w.val)','(weapon : True)'),
            ('(safe : ∀ b, b ∈ DeathSetter.writes (E1M1WeaponReadyReset.call s).core → BlockSummary.Apart ((E1M1WeaponReadyReset.call s).core.regs 1+112) b)','(safe : True)'),
            ('(low : ¬WeaponReadyGate.lowering (E1M1WeaponReadyReset.afterReset s).core)','(low : True)'),
            ('(a : WeaponReadyGate.attack (E1M1WeaponReadyReset.afterReset s).core=0)','(a : True)'),
            ('n≤24','n≤23'),('n≤89','n≤88'),('ActorSetterReturn.result p s ret','ActorSetterReturn.result p s 0x2a3f1')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_state_extraction(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.table_data(binary,p,self.spec),self.state)
        for field,value in [('index',150),('offset','0x16a90'),('hex','00'*28)]:
            spec=copy.deepcopy(self.spec);spec['state'][field]=value
            with self.assertRaises(ValueError):proof.table_data(binary,p,spec)
    def test_nonvacuous_reset_and_returns(self):
        s=(ROOT/'tests/reference/original-weapon-ready-reset.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('afterReset.pc=0x2d319','afterReset.pc=0x2a3f1'),
            ('(0x16a74,0xffffffff,28,0)','(0x16a74,1,28,0)'),('final.core.regs 4=17','final.core.regs 4=13'),('final.pc=0x2dc95','final.pc=0x2dc96')]:
            self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

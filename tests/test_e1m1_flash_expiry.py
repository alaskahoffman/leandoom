"""Universal flash-expiry contracts, nonvacuity and original table binding."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_flash_expiry as proof

class FlashExpiryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-psprite-light.json').read_text())
        exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.light.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
        cls.raw=proof.light.extraction.extract(binary,exe,cls.spec);cls.tables=proof.light.table_data(binary,exe,cls.spec)
    def lean(self,s,contracts=False):
        if contracts:
            first,rest=s.split('\n',1)
            s=first+'''\nset_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Doom.Proofs.E1M1FlashUpdate.observe Doom.Proofs.WeaponFlash.observe Doom.Weapon.tickFlash
'''+rest
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw,self.tables,self.spec),True)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('expired_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_contracts(self):
        s=proof.certificate(self.raw,self.tables,self.spec)
        for old,new in [('(tables : E1M1FlashExpiry.Tables s.memory)','(tables : True)'),
                        ('(sep : E1M1FlashExpiry.Separated p (s.regs 4))','(sep : True)'),
                        ('(h : E1M1FlashUpdate.Inputs s p v)','(h : True)'),
                        ('(supported : WeaponFlash.Supported v)','(supported : True)'),
                        ('(nonempty : v.flash.frame≠0)','(nonempty : True)'),
                        ('(expires : v.flash.tics.toBitVec=(1#32))','(expires : True)'),
                        ('¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables s.memory ∧ E1M1FlashExpiry.Separated p (s.regs 4)','True'),
                        ('n ≤ 106','n ≤ 105'),('⟨s,f,0x2dc6f⟩','⟨s,f,0x2dc60⟩'),
                        ('E1M1FlashUpdate.observe t.core.memory p','E1M1FlashUpdate.observe s.memory p')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new),True)
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout)
                self.assertNotIn('timeout',r.stdout.lower())
    def test_tables(self):
        # Isolate the new initial-memory contract from the existing table lemmas.
        s=proof.certificate(self.raw,self.tables,self.spec)
        start=s.index('theorem bytes_checked');end=s.index('theorem expiry_tables_checked')
        s=s[:start]+s[end:s.index('theorem expired_checked')]+'end Doom.Verification.ExtractedPspriteLight\n'
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for name in self.tables:
            for offset in [8,12,16,20]:
                # Pistol/first shotgun only have their successors read on expiry.
                if name not in ['lightdone','shotgunflash2'] and offset!=16:
                    continue
                tables=dict(self.tables);bs=bytearray(tables[name]);bs[offset]^=1;tables[name]=bytes(bs)
                changed=proof.certificate(self.raw,tables,self.spec)
                a=changed.index('theorem bytes_checked');b=changed.index('theorem expiry_tables_checked')
                changed=changed[:a]+changed[b:changed.index('theorem expired_checked')]+'end Doom.Verification.ExtractedPspriteLight\n'
                with self.subTest(table=name,offset=offset):
                    r=self.lean(changed);self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_nonvacuous_layout_and_expiry_results(self):
        s=(ROOT/'tests/reference/e1m1-flash-expiry.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('0x603000,0x15d8c,3,2','0x603000,0x15d8c,3,1'),
                        ('0x603000,0,0,0','0x603000,0,1,0'),
                        ('Separated 0x600100 0x603000','Separated 0x600100 (0x600100+248)')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)

if __name__=='__main__':unittest.main()

"""Weapon/flash seam, initial-memory transport and production tick contracts."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_weapon_flash as proof

class WeaponFlashTests(unittest.TestCase):
    def lean(self,s,contracts=False):
        if contracts:
            first,rest=s.split('\n',1)
            s=first+'''\nset_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Doom.Proofs.E1M1FlashUpdate.observe Doom.Proofs.WeaponFlash.observe Doom.Weapon.tick Doom.Weapon.tickFlash
'''+rest
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(),True);self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('quiet_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_contracts(self):
        s=proof.certificate()
        for old,new in [('(pc : s.pc=0x2dc95)','(pc : True)'),
                        ('(h : E1M1WeaponFlash.Boundary s.core p v)','(h : True)'),
                        ('(h : E1M1WeaponFlash.Inputs s p c.state)','(h : True)'),
                        ('(quiet : E1M1WeaponFlash.Quiet c.state)','(quiet : True)'),
                        ('(supported : WeaponFlash.Supported c.state)','(supported : True)'),
                        ('(safe : E1M1WeaponFlash.Safe p (s.regs 4))','(safe : True)'),
                        ('¬ E1M1FlashUpdate.NoTransition c.state → E1M1FlashExpiry.Tables s.memory ∧ E1M1FlashExpiry.Separated p (s.regs 4)','True'),
                        ('(earlier : ∃ n, n ≤ budget ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s u)','(earlier : True)'),
                        ('n ≤ 110','n ≤ 109'),('n ≤ 125','n ≤ 124'),('budget+110','budget+109'),
                        ('⟨s,f,0x2dc6f⟩','⟨s,f,0x2dc60⟩'),
                        ('WeaponFlash.observe (Weapon.tick c).state','WeaponFlash.observe c.state')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new),True)
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout)
                self.assertNotIn('timeout',r.stdout.lower())
    def test_nonvacuous_transport(self):
        s=(ROOT/'tests/reference/e1m1-weapon-flash.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('Safe 0x600101 5','Safe 0x600101 (0x600101+252)'),
                        ('weapon.tics=1','weapon.tics=2'),('flash.tics=6','flash.tics=7')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)

if __name__=='__main__':unittest.main()

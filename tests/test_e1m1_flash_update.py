"""Binary-to-production flash contracts, audit and signed timer boundaries."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_flash_update as proof

class FlashUpdateTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('live_correspondence','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_contracts(self):
        s=proof.certificate().replace('namespace Doom.Verification.ExtractedFlashUpdate', '''set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Doom.Proofs.E1M1FlashUpdate.observe Doom.Proofs.WeaponFlash.observe Doom.Weapon.tickFlash
namespace Doom.Verification.ExtractedFlashUpdate''')
        for old,new in [('(h : E1M1FlashUpdate.Inputs s p v)','(h : True)'),
                        ('(supported : WeaponFlash.Supported v)','(supported : True)'),
                        ('(quiet : E1M1FlashUpdate.NoTransition v)','(quiet : True)'),
                        ('n ≤ 29','n ≤ 28'),('⟨s,f,0x2dc6f⟩','⟨s,f,0x2dc60⟩'),
                        ('E1M1FlashUpdate.observe t.core.memory p','E1M1FlashUpdate.observe s.memory p')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0,r.stdout+r.stderr)
                self.assertIn('error:',r.stdout);self.assertNotIn('timeout',r.stdout.lower())
    def test_boundaries(self):
        s=(ROOT/'tests/reference/e1m1-flash-update.lean').read_text();r=self.lean(s)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('flash.frame=31','flash.frame=30'),('flash.tics=2147483647','flash.tics=(-2147483648)'),
                        ('extraLight=2','extraLight=1'),('flash.y.raw=456','flash.y.raw=0')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)

if __name__=='__main__':unittest.main()

"""Certificates, fail-closed chains, and exact state continuity."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_psprite_chain as proof

class PspriteChainTests(unittest.TestCase):
    def lean(self,s,contracts=False):
        with tempfile.TemporaryDirectory() as d:
            if contracts:
                first,rest=s.split('\n',1)
                s=first+'\nset_option backward.isDefEq.respectTransparency true\nattribute [local irreducible] Doom.Proofs.E1M1PspriteChain.chain Doom.Proofs.E1M1PspriteChain.complete Doom.Proofs.E1M1PspriteChain.slot Doom.Proofs.E1M1PspriteChain.suffix\n'+rest
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(),True);self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('chain_mono','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_contracts(self):
        s=proof.certificate()
        for old,new in [('(ok : E1M1PspriteChain.chain fuel s=some t)','(ok : True)'),
                        ('28*fuel+4','28*fuel+3'),('28*fuel+13','28*fuel+12'),('28*fuel+46','28*fuel+45'),
                        ('(pc : s.pc=0x2dc95)','(pc : True)'),('(weaponIndex : s.core.regs 6=(0#32))','(weaponIndex : True)'),
                        ('(ok : E1M1PspriteChain.suffix fuel s=some t)','(ok : E1M1PspriteChain.suffix fuel s=some s)')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new),True)
                self.assertNotEqual(r.returncode,0,r.stdout+r.stderr);self.assertIn('error:',r.stdout);self.assertNotIn('timeout',r.stdout.lower())
    def test_fail_closed_and_terminal_results(self):
        s=(ROOT/'tests/reference/e1m1-psprite-chain.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('chain 4 (start 0 1 0)).isNone=true','chain 4 (start 0 1 0)).isNone=false'),
                        ('chain 3 (start 1 0 0x2d09a)).isNone=true','chain 3 (start 1 0 0x2d09a)).isNone=false'),
                        ('some (0,0x60300c,0)','some (0,0x603008,0)')]:
            with self.subTest(change=new):
                self.assertIn(old,s);r=self.lean(s.replace(old,new))
                self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)

if __name__=='__main__':unittest.main()

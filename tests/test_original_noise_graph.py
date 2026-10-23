"""Signed DOS side lookup, graph closure and actual checked child entry."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_graph as proof
class NoiseGraphTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('entry_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts(self):
        s=proof.certificate()
        for old,new in [('(allocation : Allocation table stack)','(allocation : True)'),
            ('(room : StackRoom stack s)','(room : True)'),
            ('(rep : EdgeRep base e s.memory)','(rep : True)'),
            ('(two : e.two)','(two : True)'),
            ('(safe : Protect (edgeReads base e) [s.regs 4])','(safe : True)'),
            ('(covered : Covered table edges)','(covered : True)'),
            ('(closed : Closed table edges)','(closed : True)'),
            ('(cursor : Cursor sector s)','(cursor : True)'),
            ('(saved : E1M1NoiseOpeningFrame.CallerSafe s)','(saved : True)'),
            ('(count : s.regs 1=0 ∨ s.regs 1=1)','(count : True)'),
            ('(safe : Protect (graphReads base edges) w)','(safe : True)'),
            ('(call : (E1M1NoiseIteration.dispatched s).pc=0x26f60)','(call : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def fixture(self):
        return (ROOT/'tests/reference/original-noise-graph.lean').read_text()
    def test_actual_dispatch_both_neighbors_signed_indices_and_blocking(self):
        r=self.lean(self.fixture());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_corrupt_graph_memory_rejected(self):
        full=self.fixture()
        s=full.split('theorem allocated')[0]+'open E1M1NoiseGraph\n'+full.split('open E1M1NoiseGraph\n')[1].split('theorem graph_parent')[0]+'end Doom.Verification.NoiseGraphFixture\n'
        for old,new in [('(0x2c118,sides)','(0x2c118,sides+18)'),
            ('(wall+16,4)','(wall+16,68)'),
            ('(wall+22,65536)','(wall+22,0)'),
            ('(sides+32,other)','(sides+32,0x777777)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_missing_coverage_and_escaping_endpoint_rejected(self):
        prefix='''import Doom.Proofs.E1M1NoiseGraph
open Doom.Proofs Doom.Verification X86 X86Memory E1M1NoiseMap E1M1NoiseGraph
set_option backward.isDefEq.respectTransparency false
def sector : SectorLines := ⟨100,200,[300]⟩
def edge : Edge := ⟨300,4,0,1,100,999⟩
'''
        for claim,body in [
            ('Covered [sector] []','simp [Covered,sector]'),
            ('Closed [sector] [edge]','simp [Closed,edge,Edge.two,E1M1NoiseMapGuards.layout,sector]'),
        ]:
            with self.subTest(claim=claim):
                r=self.lean(prefix+'example : '+claim+' := by '+body+'\n')
                self.assertNotEqual(r.returncode,0);self.assertIn('unsolved goals',r.stdout)
        # A one-sided line is allowed to have an unusable back endpoint because
        # dispatch skips it before neighbor selection.
        r=self.lean(prefix+'''example : Closed [sector] [{edge with flags := 0}] := by
  simp [Closed,edge,Edge.two]
''');self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

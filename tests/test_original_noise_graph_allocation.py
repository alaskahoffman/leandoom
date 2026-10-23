"""Static graph storage replaces local and recursive write-separation premises."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_graph_allocation as proof
class NoiseGraphAllocationTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('budget_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_contracts(self):
        s=proof.certificate()
        for old,new in [('(storage : Storage table stack base edges regions)','(storage : True)'),
            ('(allocation : Allocation table stack)','(allocation : True)'),
            ('(room : StackRoom stack s)','(room : True)'),
            ('(member : s.regs 0∈layout table)','(member : True)'),
            ('(trace : CheckedTrace (layout table) phase s t w n)','(trace : True)'),
            ('(reserve : Reserve stack phase n s)','(reserve : True)'),
            ('(closed : Closed table edges)','(closed : True)'),
            ('(graph : GraphRep base edges s.core.memory)','(graph : True)'),
            ('(ledger : Represents generation s.core.memory xs)','(ledger : True)'),
            ('56*table.length+20','28*table.length+20'),
            ('2*table.length*(limit+1)+1','table.length*(limit+1)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def fixture(self):
        return (ROOT/'tests/reference/original-noise-graph-allocation.lean').read_text()
    def test_recursive_graph_preservation_child_entry_and_joined_budget(self):
        r=self.lean(self.fixture());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def placement_fixture(self):
        full=self.fixture()
        return full.split('theorem allocated')[0]+'open E1M1NoiseGraph E1M1NoiseGraphAllocation\n'+full.split('open E1M1NoiseGraph E1M1NoiseGraphAllocation\n')[1].split('theorem graph_initial')[0]+'end Doom.Verification.NoiseGraphAllocationFixture\n'
    def test_missing_truncated_or_wrapping_storage_rejected(self):
        s=self.placement_fixture()
        for old,new in [('⟨0x2c118,0x2c11c⟩,',''),
            ('0x2c11c','0x2c11b'),
            ('0x601037','0x60101c'),
            ('0x600825','0x600824'),
            ('0x2c11c','0x100000001'),
            ('⟨wall,4,0,1,origin,origin⟩','⟨wall,4,0,2,origin,origin⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('unsolved goals',r.stdout)
    def test_aliasing_sector_stack_or_opening_globals_rejected(self):
        s=self.placement_fixture()
        for old,new in [('⟨0x601001,0x601037⟩','⟨0x600201,0x601037⟩'),
            ('⟨0x70007d,0x700105⟩','⟨0x601036,0x700105⟩'),
            ('⟨0x2c118,0x2c11c⟩','⟨0x2c03b,0x2c11c⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('unsolved goals',r.stdout)
if __name__=='__main__':unittest.main()

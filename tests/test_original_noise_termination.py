"""Construct original recursive traversals without supplying execution traces."""
import subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_termination as proof
class NoiseTerminationTests(unittest.TestCase):
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate());self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('total_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_required_entry_and_static_contracts(self):
        s=proof.certificate()
        for old,new in [('(allocation : Allocation table stack)','(allocation : True)'),
            ('(storage : Storage table stack base edges regions)','(storage : True)'),
            ('(bounds : Bounded table limit)','(bounds : True)'),
            ('(covered : Covered table edges)','(covered : True)'),
            ('(closed : Closed table edges)','(closed : True)'),
            ('(shape : addresses xs=layout table)','(shape : True)'),
            ('(ledger : Represents generation s.core.memory xs)','(ledger : True)'),
            ('(map : MapRep table s.core.memory)','(map : True)'),
            ('(graph : GraphRep base edges s.core.memory)','(graph : True)'),
            ('(member : s.core.regs 0∈layout table)','(member : True)'),
            ('(count : s.core.regs 2=0 ∨ s.core.regs 2=1)','(count : True)'),
            ('(reserve : Reserve stack phase (credit xs) s)','(reserve : True)'),
            ('(pc : s.pc=0x26f60)','(pc : True)'),
            ('56*table.length+20','28*table.length+20'),
            ('2*table.length*(limit+1)+1','table.length*(limit+1)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def fixture(self):
        return (ROOT/'tests/reference/original-noise-termination.lean').read_text()
    def short_fixture(self):
        return self.fixture().split('-- The first child')[0]+'end Doom.Verification.NoiseTerminationFixture\n'
    def test_admitted_child_cyclic_graph_and_original_return(self):
        r=self.lean(self.fixture());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_blocked_and_one_sided_graphs(self):
        for flags in [68,0]:
            with self.subTest(flags=flags):
                s=self.short_fixture().replace('(wall+16,4)',f'(wall+16,{flags})').replace('⟨wall,4,0,1,origin,other⟩',f'⟨wall,{flags},0,1,origin,other⟩')
                r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_empty_sector_and_already_visited_entry(self):
        s=self.short_fixture()
        variants=[s.replace('(origin+78,2)','(origin+78,0)').replace('⟨origin,0x600b01,[wall,wall]⟩','⟨origin,0x600b01,[]⟩'),
            s.replace('(origin+66,6),(origin+18,0)','(origin+66,7),(origin+18,1)').replace('[(origin,.unseen),(other,.unseen)]','[(origin,.clear),(other,.unseen)]')]
        for variant in variants:
            r=self.lean(variant);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_inconsistent_graph_ledger_count_and_insufficient_space_rejected(self):
        s=self.short_fixture()
        variants=[s.replace('(0x13580,7)','(0x13580,8)'),
            s.replace('if r=2 then 0','if r=2 then 2'),
            s.replace('0x70007d','0x70007e'),
            s.replace('(sides+32,other)','(sides+32,0x600301)').replace('⟨wall,4,0,1,origin,other⟩','⟨wall,4,0,1,origin,0x600301⟩'),
            s.replace('0x601037','0x601018')]
        for i,variant in enumerate(variants):
            with self.subTest(variant=i):
                r=self.lean(variant);self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

"""Raw initial header contracts, counter framing, and nonvacuous composition."""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_heap as proof
import test_original_group_handoff as harness


class GroupHeapTests(unittest.TestCase):
    lean = harness.GroupHandoffTests.lean
    rejects = harness.GroupHandoffTests.rejects

    @classmethod
    def setUpClass(cls):
        cls.raw = {}
        for name in ['handoff','split','count','malloc']:
            spec = json.loads((ROOT/f'tests/reference/original-group-{name}.json').read_text())
            for key,unit in spec['units'].items():
                if name=='malloc' and key=='entry': key='malloc_entry'
                cls.raw[key] = bytes.fromhex(unit['hex'])
        cls.fixture = (ROOT/'tests/reference/original-group-heap.lean').read_text()

    def passes(self, source):
        result = self.lean(source)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertNotIn('sorryAx',result.stdout)
        self.assertNotIn('_native',result.stdout)
        return result

    def test_certificate_and_strict_audit(self):
        result = self.passes(proof.certificate(self.raw))
        proof.audit(result.stdout)
        for bad in [result.stdout+'extra',result.stdout.replace('ready_checked','missing'),
                    result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','bad._native.ax_1')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_initial_memory_count_separation_and_conditions_required(self):
        source = proof.certificate(self.raw)
        for old,new in [
            ('(heap : v.Holds s.memory)','(heap : True)'),
            ('(safe : ∀ w∈v.words, OriginalGroupCountScan.SafeWord w.1 es)','(safe : True)'),
            ('(conditions : OriginalGroupHeap.Conditions v (OriginalGroupHeap.request es) (s.regs 4))',
             '(conditions : True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,source); self.rejects(source.replace(old,new))

    def test_concrete_count_to_allocation_from_raw_headers(self):
        self.passes(self.fixture)

    def test_predecessor_split_threshold_and_wrapping_stack(self):
        for previous,size,sp in [(False,92,8),(True,93,0x680000),(True,4096,8)]:
            source = self.fixture
            if previous:
                source = source.replace('(0x621004,2)',
                    '(0x621004,0),(0x621014,0x622000),(0x621000,4096),(0x621010,0x622100)')
                source = source.replace('0x621000,2,0x621000,4096','0x621000,0,0x622000,4096')
            source = source.replace('4096',str(size)).replace('0x680000',hex(sp))
            with self.subTest(previous=previous,size=size,sp=sp): self.passes(source)

    def test_bad_raw_headers_capacity_and_stack_rejected(self):
        for old,new in [('(0x621004,2)','(0x621004,3)'),
                        ('4096','27'),('0x680000','0x620008')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture); self.rejects(self.fixture.replace(old,new))

    def test_wrong_results_rejected(self):
        for old,new in [('memory 0xa04e=1','memory 0xa04e=2'),
                        ('core.regs 1=28','core.regs 1=24'),
                        ('core.regs 4+16)=0x2e63e','core.regs 4+16)=0x2e63f')]:
            with self.subTest(change=old):
                self.assertIn(old,self.fixture); self.rejects(self.fixture.replace(old,new))

    def test_counter_overlapping_heap_global_rejected(self):
        # This counter is at front+78 = 0x74fe0, exactly the main-zone pointer.
        # Limit the fixture to the initial proofs, so failure cannot come from
        # a later expected counter value or the allocation result.
        prefix = self.fixture[:self.fixture.index('theorem conditions :')]
        source = prefix.replace('0xa000','0x74f92')+'end Doom.Tests.GroupHeap\n'
        self.rejects(source)


if __name__=='__main__': unittest.main()

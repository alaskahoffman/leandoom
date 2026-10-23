"""Actual allocator CALL, rounding, first-free contracts and counting composition."""
import copy
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_group_malloc as proof
import test_original_group_handoff as harness


class GroupMallocTests(unittest.TestCase):
    lean = harness.GroupHandoffTests.lean
    rejects = harness.GroupHandoffTests.rejects

    @classmethod
    def setUpClass(cls):
        cls.spec = json.loads((ROOT/'tests/reference/original-group-malloc.json').read_text())
        cls.raw = {'call': bytes.fromhex(cls.spec['units']['call']['hex']),
                   'malloc_entry': bytes.fromhex(cls.spec['units']['entry']['hex'])}
        for name in ['handoff', 'split', 'count']:
            spec = json.loads((ROOT/f'tests/reference/original-group-{name}.json').read_text())
            cls.raw.update({n:bytes.fromhex(v['hex']) for n,v in spec['units'].items()})
        cls.fixture = (ROOT/'tests/reference/original-group-malloc.lean').read_text()

    def test_certificate_and_strict_audit(self):
        result = self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout+'extra', result.stdout.replace('startup_checked','missing'),
                    result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','bad._native.ax_1')]:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_call_rounding_branch_and_count_bytes_bound(self):
        # CALL displacement, AND CL mask, header size, predecessor branch, count.
        for key, offset in [('call',1), ('malloc_entry',27), ('malloc_entry',33),
                            ('malloc_entry',37), ('count',0)]:
            with self.subTest(key=key, offset=offset):
                raw = dict(self.raw)
                changed = bytearray(raw[key]); changed[offset] ^= 1
                raw[key] = bytes(changed)
                self.rejects(proof.certificate(raw))

    def test_heap_and_caller_contracts_required(self):
        source = proof.certificate(self.raw)
        for old in ['(h : OriginalGroupMalloc.Ready s)', '(user : s.regs 3=(0#32))',
                    '(tag : s.regs 2=(50#32))',
                    '(heap : OriginalGroupMalloc.Ready (OriginalGroupCountScan.final es s).core)']:
            with self.subTest(premise=old):
                self.assertIn(old, source)
                self.rejects(source.replace(old, old.split(':')[0]+': True)'))

    def test_concrete_count_call_allocation_and_return(self):
        result = self.lean(self.fixture)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertNotIn('sorryAx',result.stdout)
        self.assertNotIn('_native',result.stdout)

    def test_wrong_count_return_and_rounding_rejected(self):
        for old,new in [('memory 0xa04e=1','memory 0xa04e=2'),
                        ('core.regs 4+16)=0x2e63e','core.regs 4+16)=0x2e63f'),
                        ('core.regs 1=28','core.regs 1=24'),
                        ('rounded 0xfffffffc=20','rounded 0xfffffffc=24')]:
            with self.subTest(change=old):
                self.assertIn(old,self.fixture)
                self.rejects(self.fixture.replace(old,new))

    def test_undersized_occupied_or_exhausted_heap_rejected(self):
        for old,new in [('(0x620000,4096)','(0x620000,27)'),
                        ('(0x620000,4096)','(0x620000,4096),(0x620004,2)'),
                        ('(0x620014,0x621000)','(0x620014,0x620000)')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture)
                self.rejects(self.fixture.replace(old,new))

    def test_extraction_mapping_and_relocations(self):
        profile = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary = proof.extraction.original.extract(ROOT/shareware['local_directory']/'doom19s.zip',shareware,profile)
        raw = proof.extraction.extract(binary,profile,self.spec)
        self.assertEqual(raw['call'],self.raw['call'])
        self.assertEqual(raw['entry'],self.raw['malloc_entry'])
        for mode in ['byte','mapping','fixup']:
            bad = copy.deepcopy(self.spec); unit = bad['units']['entry']
            if mode=='byte': unit['hex']='90'+unit['hex'][2:]
            elif mode=='mapping': unit['file_offset']=hex(int(unit['file_offset'],16)+1)
            else: unit['relocations']=unit['relocations'][:-1]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                proof.extraction.extract(binary,profile,bad)


if __name__=='__main__': unittest.main()

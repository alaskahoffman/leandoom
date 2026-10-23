"""Owned allocation, generated successor headers, and explicit caller boundary."""
import json
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_remainder as proof
import test_original_group_handoff as harness


class GroupRemainderTests(unittest.TestCase):
    lean=harness.GroupHandoffTests.lean
    rejects=harness.GroupHandoffTests.rejects

    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['handoff','split','count','malloc']:
            spec=json.loads((ROOT/f'tests/reference/original-group-{name}.json').read_text())
            for key,unit in spec['units'].items():
                if name=='malloc' and key=='entry':key='malloc_entry'
                cls.raw[key]=bytes.fromhex(unit['hex'])
        cls.fixture=(ROOT/'tests/reference/original-group-remainder.lean').read_text()

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout+'extra',result.stdout.replace('view_checked','missing'),
                    result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','bad._native.ax_1')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_owned_branch_bytes_are_bound(self):
        for offset in [6,9,11]:
            raw=dict(self.raw);b=bytearray(raw['allocation']);b[offset]^=1;raw['allocation']=bytes(b)
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))

    def test_nonzero_owner_and_shape_contracts_required(self):
        source=proof.certificate(self.raw)
        for old,new in [('(user : s.regs 7≠(0#32))','(user : True)'),
                        ('(conditions : OriginalGroupRemainder.Conditions p s.memory)','(conditions : True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_concrete_predecessor_and_following_allocation(self):
        result=self.lean(self.fixture)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertNotIn('sorryAx',result.stdout);self.assertNotIn('_native',result.stdout)

    def test_bad_owner_split_boundary_and_alias_rejected(self):
        for old,new in [('928,11071584,50','928,0,50'),
                        ('6445464,928','992,928'),
                        ('928,11071584,50','928,4621968,50')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture);self.rejects(self.fixture.replace(old,new))

    def test_wrong_published_value_and_remainder_rejected(self):
        for old,new in [('memory 11071584=4621988','memory 11071584=4621992'),
                        ('memory 4622892=6444536','memory 4622892=6444532')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture);self.rejects(self.fixture.replace(old,new))

    def test_following_call_cannot_use_unmodified_heap(self):
        old='    (plan.result initial).core.memory⟩'
        self.assertIn(old,self.fixture)
        self.rejects(self.fixture.replace(old,'    initial.memory⟩'))


if __name__=='__main__':unittest.main()

"""Actual owned RET, saved registers, caller arguments and return-slot reuse."""
import copy
import json
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_return as proof
import test_original_group_handoff as harness


class GroupReturnTests(unittest.TestCase):
    lean=harness.GroupHandoffTests.lean
    rejects=harness.GroupHandoffTests.rejects

    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['handoff','split','count','malloc','return']:
            spec=json.loads((ROOT/f'tests/reference/original-group-{name}.json').read_text())
            for key,unit in spec['units'].items():
                if name=='malloc' and key=='entry':key='malloc_entry'
                cls.raw[key]=bytes.fromhex(unit['hex'])
        cls.spec=spec
        cls.fixture=(ROOT/'tests/reference/original-group-return.lean').read_text()

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout+'extra',result.stdout.replace('read_arguments','missing'),
                    result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','bad._native.ax_1')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_restore_and_caller_bytes_bound(self):
        for key,offset in [('allocation',64),('allocation',68),('cache_call',7),('cache_call',11)]:
            raw=dict(self.raw);b=bytearray(raw[key]);b[offset]^=1;raw[key]=bytes(b)
            with self.subTest(key=key,offset=offset):self.rejects(proof.certificate(raw))

    def test_saved_return_and_frame_contracts_required(self):
        source=proof.certificate(self.raw)
        for old,new in [('(safe : OriginalGroupReturn.FrameSafe p s)','(safe : True)'),
                        ('(ret : load32 s.memory (s.regs 4+16)=0x38d41)','(ret : True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,source);self.rejects(source.replace(old,new))

    def test_concrete_join_arguments_and_slot_reuse(self):
        result=self.lean(self.fixture)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertNotIn('sorryAx',result.stdout);self.assertNotIn('_native',result.stdout)

    def test_wrong_saved_return_index_or_offset_rejected(self):
        for old,new in [('(0x680010,0x38d41)','(0x680010,0x38d42)'),
                        ('(0x68000c,15)','(0x68000c,16)'),
                        ('(0x680008,60)','(0x680008,64)')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture);self.rejects(self.fixture.replace(old,new))

    def test_wrong_pointer_stack_and_new_return_rejected(self):
        for old,new in [('core.regs 2=4621988','core.regs 2=4621992'),
                        ('core.regs 4=0x680010','core.regs 4=0x680014'),
                        ('memory 0x680010=0x38d50','memory 0x680010=0x38d41')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture);self.rejects(self.fixture.replace(old,new))

    def test_extraction_mapping_and_fixup(self):
        extraction=proof.prior.heap.malloc.extraction
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(extraction.extract(binary,profile,self.spec)['cache_call'],self.raw['cache_call'])
        for mode in ['byte','mapping','fixup']:
            bad=copy.deepcopy(self.spec);unit=bad['units']['cache_call']
            if mode=='byte':unit['hex']='90'+unit['hex'][2:]
            elif mode=='mapping':unit['file_offset']=hex(int(unit['file_offset'],16)+1)
            else:unit['relocations']=[]
            with self.subTest(mode=mode),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)


if __name__=='__main__':unittest.main()

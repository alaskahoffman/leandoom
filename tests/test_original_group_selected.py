"""Candidate rejection, split boundary, lifetime-correct contracts and composition."""
import copy,json,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_selected as proof
import test_original_group_handoff as harness

class GroupSelectedTests(unittest.TestCase):
    lean=harness.GroupHandoffTests.lean
    rejects=harness.GroupHandoffTests.rejects
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-group-split.json').read_text())
        old=json.loads((ROOT/'tests/reference/original-group-handoff.json').read_text())
        cls.raw={n:bytes.fromhex(v['hex']) for n,v in (cls.spec['units']|old['units']).items()}
        cls.fixture=(ROOT/'tests/reference/original-group-selected.lean').read_text()
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout+'extra',r.stdout.replace('selected_checked','missing'),r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_new_bytes_and_threshold_are_bound(self):
        for offset in [0,18,20]:
            raw=dict(self.raw);b=bytearray(raw['select_split']);b[offset]^=1;raw['select_split']=bytes(b)
            with self.subTest(offset=offset):self.rejects(proof.certificate(raw))
    def test_candidate_and_return_contracts_required(self):
        s=proof.certificate(self.raw)
        for old,new in [
          ('(free : load32 s.memory (s.regs 3+(4#32))=(0#32))','(free : True)'),
          ('(fits : (s.regs 1).toInt≤(OriginalGroupSplit.candidateSize s).toInt)','(fits : True)'),
          ('(safe : OriginalGroupSelected.ReturnSafe s)','(safe : True)')]:
            with self.subTest(premise=old):self.assertIn(old,s);self.rejects(s.replace(old,new))
    def test_nonvacuous_join_split_links_and_thresholds(self):
        r=self.lean(self.fixture);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertNotIn('sorryAx',r.stdout);self.assertNotIn('_native',r.stdout)
    def test_wrong_boundary_links_and_count_rejected(self):
        for old,new in [('initial 2656','initial 2657'),
                        ('memory 0x620a20=65','memory 0x620a20=64'),
                        ('memory 0x620f14=0x620a20','memory 0x620f14=0x620a24'),
                        ('memory 0x63004e=3','memory 0x63004e=4')]:
            with self.subTest(change=old):self.assertIn(old,self.fixture);self.rejects(self.fixture.replace(old,new))
    def test_wrong_candidate_and_saved_return_rejected(self):
        for old,new in [('def start := initial 3000','def start := initial 2591'),
                        ('(0x680010,0x2e63e)','(0x680010,0x2e63f)')]:
            with self.subTest(change=old):self.assertIn(old,self.fixture);self.rejects(self.fixture.replace(old,new))
    def test_extraction_and_fixups(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec)['select_split'],self.raw['select_split'])
        for mode in ['byte','mapping','fixup']:
            bad=copy.deepcopy(self.spec);u=bad['units']['select_split']
            if mode=='byte':u['hex']='90'+u['hex'][2:]
            elif mode=='mapping':u['file_offset']=hex(int(u['file_offset'],16)+1)
            else:u['relocations']=[dict(offset=0,object=3,target='0x74fe0')]
            with self.subTest(mode=mode),self.assertRaises(ValueError):proof.extraction.extract(binary,p,bad)
if __name__=='__main__':unittest.main()

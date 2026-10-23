"""Machine bytes, alias ordering, count rule and non-vacuous frame premises."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_count as proof
class GroupCountTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={'count':bytes.fromhex(json.loads((ROOT/'tests/reference/original-group-count.json').read_text())['units']['count']['hex'])}
        cls.fixture=(ROOT/'tests/reference/original-group-count.lean').read_text()
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('iteration_path','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_extraction_rejects_mapping_and_relocation_changes(self):
        import copy
        spec=json.loads((ROOT/'tests/reference/original-group-count.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,spec),self.raw)
        for mutation in ['offset','relocation']:
            bad=copy.deepcopy(spec)
            if mutation=='offset':bad['units']['count']['file_offset']='0x70604'
            else:bad['units']['count']['relocations'][0]['target']='0x2c124'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,profile,bad)
    def test_mutated_original_byte_rejected(self):
        raw={'count':self.raw['count'].replace(bytes.fromhex('ff434e'),bytes.fromhex('ff434f'))}
        self.assertNotEqual(raw,self.raw);r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_counter_and_alias_fixtures(self):
        r=self.lean(self.fixture);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertNotIn('sorryAx',r.stdout);self.assertNotIn('_native',r.stdout)
    def test_wrong_double_count_and_stale_read_rejected(self):
        for old,new in [('(result (initial 0xa000)).core.regs 2=0','(result (initial 0xa000)).core.regs 2=1'),
                        ('back aliases=0xb001','back aliases=0xb000'),
                        ('(result wraps).pc=0x2e602','(result wraps).pc=0x2e62b')]:
            with self.subTest(claim=old):
                self.assertIn(old,self.fixture);r=self.lean(self.fixture.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_frame_requires_storage_separation(self):
        r=self.lean(self.fixture.replace('(h : Protected a s)','(h : True)'))
        self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

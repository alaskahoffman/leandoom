"""Original loader bytes, signed pointer conversion and memory-order contracts."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_side_loader as proof
class SideLoaderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-side-loader.json').read_text())
        cls.raw={k:bytes.fromhex(u['hex']) for k,u in cls.spec['units'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('pointer_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_instruction_bytes_rejected(self):
        for name,offset in [('publish',3),('link',3),('link',6),('link',7),('link',33)]:
            with self.subTest(name=name,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_required_contracts_and_result(self):
        s=proof.certificate(self.raw)
        for old,new in [('(source : load16 s.memory (s.regs 3+28)=index)','(source : True)'),
            ('(sectors : load32 s.memory 0x2c148=base)','(sectors : True)'),
            ('(safe : Apart 0x2c148 (s.regs 4))','(safe : True)'),
            ('(valid : index.toNat<32768)','(valid : True)'),
            ('index.toNat*86','index.toNat*85'),
            ('[0x2e4d1] 11','[0x2e4d1] 10')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_extraction_mapping_and_relocations(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),self.raw)
        for field,value in [('code_offset','0x2e4b0'),('file_offset','0x704c4'),('hex','90'),('relocations',[])]:
            with self.subTest(field=field):
                spec=copy.deepcopy(self.spec);spec['units']['link'][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_signed_aliasing_and_sparse_frame_fixture(self):
        r=self.lean((ROOT/'tests/reference/original-side-loader.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

"""Pinned vertex/delta and bounds-suffix proofs, including ordered aliasing."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_geometry as proof
class LineGeometryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-line-geometry.json').read_text());cls.raw={}
        for name in ['original-line-geometry','original-line-load','original-line-cache']:
            for k,u in json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())['units'].items():cls.raw[k]=bytes.fromhex(u['hex'])
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('suffix_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_instruction_bytes_rejected(self):
        for name,offset in [('vertices',5),('vertices',22),('delta',10),('horizontal',7),('vertical',8),('copy',7),('cache',24),('advance',15)]:
            with self.subTest(name=name,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_missing_contracts_and_changed_results(self):
        s=proof.certificate(self.raw)
        for old,new in [('(h : E1M1LineLoad.Source e s)','(h : True)'),('(rawFront : SafeWord s (s.regs 1+10))','(rawFront : True)'),
            ('(base : SafeWord s 0x2c118)','(base : True)'),('[0x2e2ec] 18','[0x2e2ec] 17'),
            ('[0x2e29a,0x2e3c1] 42','[0x2e29a,0x2e3c1] 41'),('⟨s,f,0x2e326⟩','⟨s,f,0x2e358⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_extraction_mapping_and_relocations(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),{n:self.raw[n] for n in self.spec['units']})
        for name,field,value in [('vertices','code_offset','0x2e2b3'),('delta','file_offset','0x702eb'),('horizontal','hex','90'),('vertices','relocations',[])]:
            with self.subTest(name=name,field=field):
                spec=copy.deepcopy(self.spec);spec['units'][name][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_signed_bounds_aliasing_and_raw_source_fixture(self):
        r=self.lean((ROOT/'tests/reference/original-line-geometry.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_minmax_separation_is_required(self):
        s=(ROOT/'Doom/Proofs/OriginalLineGeometry.lean').read_text()
        for old,new in [('(a : Apart (s.regs 6+off) (s.regs 3+low))','(a : True)'),
            ('(b : Apart (s.regs 7+off) (s.regs 3+low))','(b : True)'),
            ('(dest : Apart (s.regs 3+low) (s.regs 3+high))','(dest : True)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

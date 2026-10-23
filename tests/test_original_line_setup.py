"""Kernel contracts for metadata and slope, plus coexistence with arithmetic."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_setup as proof
class LineSetupTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
            for k,u in json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())['units'].items():cls.raw[k]=bytes.fromhex(u['hex'])
        cls.spec=json.loads((ROOT/'tests/reference/original-line-setup.json').read_text())
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('axis_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_mutated_bytes_rejected(self):
        for name,offset in [('metadata',7),('metadata',11),('slope',5),('slope',34),('slope',40),('vertices',22),('delta',10),('horizontal',7),('vertical',8),('copy',7),('cache',24),('advance',15)]:
            with self.subTest(name=name,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_no_unconditional_axis_or_lower_budget(self):
        s=proof.certificate(self.raw)
        for old,new in [('(axis : OriginalLineSetup.dx (E1M1LineSetup.prepared s).core=0 ∨ OriginalLineSetup.dy (E1M1LineSetup.prepared s).core=0)','(axis : True)'),
            ('n≤75','n≤74'),('n≤33','n≤32'),('n≤46','n≤45'),('⟨s,f,0x2e29a⟩','⟨s,f,0x2e2b2⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_original_extraction_and_mapping(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),{n:self.raw[n] for n in self.spec['units']})
        for name,field,value in [('metadata','code_offset','0x2e29b'),('slope','file_offset','0x70301'),('slope','hex','90'),('metadata','relocations',[{'offset':0,'object':3,'target':'0x0'}])]:
            with self.subTest(name=name,field=field):
                spec=copy.deepcopy(self.spec);spec['units'][name][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_alias_order_zero_quotient_and_interpreter_coexistence(self):
        r=self.lean((ROOT/'tests/reference/original-line-setup.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

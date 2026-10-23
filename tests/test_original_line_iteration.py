"""Complete call composition, successful-division contract and ISA regressions."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_iteration as proof
class LineIterationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
            for k,u in json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())['units'].items():cls.raw[k]=bytes.fromhex(u['hex'])
        cls.data,_=proof.setup.geometry.geometry_data()
        cls.spec=json.loads((ROOT/'tests/reference/original-div-memory.json').read_text())
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw,self.data));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('iteration_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_changed_guard_stack_return_and_shift_rejected(self):
        for name,off in [('division',0),('division',26),('division',32),('division',48),('division',52),('division',59),('slope',34)]:
            with self.subTest(name=name,offset=off):
                raw=self.raw.copy();b=bytearray(raw[name]);b[off]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw,self.data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_success_contract_and_budgets_required(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(safe : OriginalDivMemory.Safe s)','(safe : True)'),('(safe : E1M1LineIteration.Safe s)','(safe : True)'),
            ('n≤25','n≤24'),('n≤104','n≤103'),('⟨s,f,0x1d180⟩','⟨s,f,0x1d183⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_original_extraction_mapping(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),{'division':self.raw['division']})
        for field,value in [('code_offset','0x1d181'),('file_offset','0x5f195'),('hex','90'),('relocations',[{'offset':0,'object':3,'target':'0x0'}])]:
            with self.subTest(field=field):
                spec=copy.deepcopy(self.spec);spec['units']['division'][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_real_stack_extremes_and_internal_return_target(self):
        r=self.lean((ROOT/'tests/reference/original-div-memory.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_new_instruction_semantics(self):
        r=self.lean((ROOT/'tests/reference/x86-div-memory.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_pinned_safety_rejects_faulting_operands(self):
        data=copy.deepcopy(self.data)
        # INT_MIN divided by -65536 overflows on the original IDIV path.
        data['geometry'][0]=(0,1,0,0,0xffff0000,0x80000000)
        r=self.lean(proof.certificate(self.raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('false',r.stdout)
if __name__=='__main__':unittest.main()

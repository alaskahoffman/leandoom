"""Initial WAD relation, safety discharge, and alias/mismatched-source regressions."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_source as proof
class LineSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
            for k,u in json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())['units'].items():cls.raw[k]=bytes.fromhex(u['hex'])
        cls.data,_=proof.scan.iteration.setup.geometry.geometry_data()
        cls.fixture=(ROOT/'tests/reference/original-line-source.lean').read_text()
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_strict_audit(self):
        s=proof.certificate(self.raw,self.data)
        # The new final theorem must not assume per-state Arithmetic or Safe.
        tail=s.split('namespace Doom.Verification.ExtractedLineSource')[1]
        self.assertNotIn('E1M1LineScan.Arithmetic',tail);self.assertNotIn('E1M1LineIteration.Safe',tail)
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('iteration_deltas','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_initial_image_and_separation_required(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(image : Image records raw base s.memory)','(image : True)'),
            ('(separate : ImageLayout records raw base line sp)','(separate : True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_all_premises_discharged_fixture(self):
        r=self.lean(self.fixture);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertNotIn('sorryAx',r.stdout);self.assertNotIn('_native',r.stdout)
    def test_wrong_initial_coordinate_and_alias_rejected(self):
        for old,new in [('(0x8010,65536)','(0x8010,65537)'),('0x7000','0x6000')]:
            with self.subTest(change=old):
                self.assertIn(old,self.fixture);r=self.lean(self.fixture.replace(old,new))
                self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_faulting_deltas_and_wrong_record_count_rejected(self):
        for kind in ['fault','missing']:
            with self.subTest(kind=kind):
                data=copy.deepcopy(self.data)
                if kind=='fault':data['geometry'][0]=(0,1,0,0,0xffff0000,0x80000000)
                else:data['geometry'].pop()
                r=self.lean(proof.certificate(self.raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

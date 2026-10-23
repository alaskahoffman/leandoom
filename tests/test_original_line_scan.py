"""Whole-loop contract, pinned bytes, and nonvacuous two-iteration fixtures."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_scan as proof
class LineScanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
            for k,u in json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())['units'].items():cls.raw[k]=bytes.fromhex(u['hex'])
        cls.data,_=proof.iteration.setup.geometry.geometry_data()
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw,self.data));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('scan_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_whole_loop_premises_cannot_be_dropped(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(layout : E1M1LineScan.Layout 475 line sp)','(layout : True)'),
            ('(initial : E1M1LineScan.Ready 475 raw line sp 0 s)','(initial : True)'),
            ('(arithmetic : E1M1LineScan.Arithmetic 475 s f)','(arithmetic : True)')]:
            with self.subTest(premise=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_wrong_fuel_entry_and_final_counter_rejected(self):
        s=proof.certificate(self.raw,self.data)
        # Mutate just the scan theorem, preserving the earlier iteration theorem.
        head,tail=s.split('namespace Doom.Verification.ExtractedLineScan')
        for old,new in [('49400','49399'),('⟨s,f,0x2e29a⟩','⟨s,f,0x2e2b2⟩'),
            ('Ready 475 raw line sp 475','Ready 475 raw line sp 474')]:
            with self.subTest(change=old):
                self.assertIn(old,tail);r=self.lean(head+'namespace Doom.Verification.ExtractedLineScan'+tail.replace(old,new))
                self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_loop_stride_and_branch_bytes_rejected(self):
        for offset in [2,7,10,len(self.raw['advance'])-1]:
            with self.subTest(offset=offset):
                raw=self.raw.copy();b=bytearray(raw['advance']);b[offset]^=1;raw['advance']=bytes(b)
                r=self.lean(proof.certificate(raw,self.data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_mixed_branches_wrapping_stack_and_frame(self):
        r=self.lean((ROOT/'tests/reference/original-line-scan.lean').read_text())
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertNotIn('sorryAx',r.stdout);self.assertNotIn('_native',r.stdout)
if __name__=='__main__':unittest.main()

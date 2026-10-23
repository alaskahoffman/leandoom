"""Original complete scan: source identity, actual path, frames and finite layout."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_scan as proof
class GroupScanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-group-lines','original-group-bounds']:
            spec=json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())
            cls.raw.update({k:bytes.fromhex(u['hex']) for k,u in spec['units'].items()})
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('scan_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_all_segment_bytes_pinned(self):
        for name in proof.UNITS:
            with self.subTest(segment=name):
                raw=self.raw.copy();b=bytearray(raw[name]);b[0]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_missing_contracts_and_wrong_bound_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('(layout : Layout 475 (s.regs 4) (s.regs 6))','(layout : True)'),
            ('(count : (load32 s.memory 0x2c134).toNat=475)','(count : True)'),
            ('(safe : Apart 0x2c134 (s.regs 5+82))','(safe : True)'),
            ('[0x2e6af] 20431','[0x2e6af] 20430'),('⟨s,f,0x2e661⟩','⟨s,f,0x2e676⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_finite_layout_is_not_vacuous(self):
        # Moving the output region onto the count must invalidate its certificate.
        s=proof.certificate(self.raw).replace('cursor 0x610000','cursor 0x2c134').replace('475 0x600800 0x610000','475 0x600800 0x2c134')
        r=self.lean(s);self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_empty_skip_self_edge_and_count_alias(self):
        r=self.lean((ROOT/'tests/reference/original-group-scan.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

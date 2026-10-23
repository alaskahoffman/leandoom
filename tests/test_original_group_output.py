"""Original scan output, WAD ordering, frame requirements and sector Rep."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_output as proof
class GroupOutputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-group-lines','original-group-bounds']:
            spec=json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())
            cls.raw.update({k:bytes.fromhex(u['hex']) for k,u in spec['units'].items()})
        cls.data=dict(rows=[[0,1,2],[0]],sides=[0,1],lines=[[0,4,0,1,0,1],[1,0,0,65535,0,0],[2,4,0,0,0,0]],limit=3)
        cls.fixture=(ROOT/'tests/reference/original-group-output.lean').read_text()
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw,self.data));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('sector_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_all_instruction_slices_pinned(self):
        for name in proof.scan.UNITS:
            with self.subTest(segment=name):
                raw=self.raw.copy();b=bytearray(raw[name]);b[0]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw,self.data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_order_and_contract_rejections(self):
        for row in [[2,1,0],[0,1,2,2],[0,2]]:
            data=copy.deepcopy(self.data);data['rows'][0]=row
            r=self.lean(proof.certificate(self.raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('false',r.stdout)
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(setup : Setup topology a i s)','(setup : True)'),
            ('(addresses : OriginalGroupLines.SectorAddresses a topology.sectors.length)','(addresses : True)'),
            ('(6+43*topology.lines.length)','(5+43*topology.lines.length)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_concrete_full_execution_and_readback(self):
        r=self.lean(self.fixture);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_overlapping_storage_and_wrong_output_rejected(self):
        for old,new in [('0x618000','0x600800'),
            ('[0x601000,0x60103e,0x60107c]','[0x60103e,0x601000,0x60107c]'),
            ('[0x601000,0x60103e,0x60107c]','[0x601000,0x60103e,0x60107c,0x60107c]')]:
            with self.subTest(change=new):
                self.assertIn(old,self.fixture);r=self.lean(self.fixture.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

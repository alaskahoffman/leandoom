"""The whole loader establishes grouping inputs, with no assumed cached output."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_output as proof
class LineOutputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw={}
        for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
            for k,u in json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())['units'].items():cls.raw[k]=bytes.fromhex(u['hex'])
        cls.data,_=proof.source.scan.iteration.setup.geometry.geometry_data()
        cls.fixture=(ROOT/'tests/reference/original-line-output.lean').read_text()
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    def test_certificate_and_strict_audit(self):
        s=proof.certificate(self.raw,self.data)
        tail=s.split('theorem scan_checked')[-1].split(' :\n    X86Routine.run')[0]
        self.assertNotIn('OriginalGroupOutput.Inputs',tail)
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('final_record','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_side_image_storage_and_address_premises_required(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(sideImage : Image (sides a) raw sideBase s.memory)','(sideImage : True)'),
            ('(sidesSafe : ImageLayout (sides a) raw sideBase output sp)','(sidesSafe : True)'),
            ('(storage : OutputLayout 475 output sp)','(storage : True)'),
            ('a.line (topology.get i).index=E1M1LineScan.cursor output 62 i.val','a.line (topology.get i).index=E1M1LineScan.cursor output 60 i.val')]:
            with self.subTest(premise=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_mixed_sides_complete_fixture(self):
        r=self.lean(self.fixture);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertNotIn('sorryAx',r.stdout);self.assertNotIn('_native',r.stdout)
    def test_wrong_side_value_and_later_stack_alias_rejected(self):
        bad_value=self.fixture.replace('(0x900e,0xa000)','(0x900e,0xa001)')
        # On the second (diagonal) record, the save slots now hit the first
        # record's cached front/back words. Source geometry remains separate.
        bad_stack=self.fixture.replace('else if r=4 then 2','else if r=4 then 0x703e').replace('0x7000 2','0x7000 0x703e').replace('(sp:=2)','(sp:=0x703e)')
        for bad in [bad_value,bad_stack]:
            r=self.lean(bad);self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_missing_topology_record_rejected(self):
        data=copy.deepcopy(self.data);data['lines'].pop()
        r=self.lean(proof.certificate(self.raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

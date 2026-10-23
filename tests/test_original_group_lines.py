"""Original group-line branches, ordered selection and publication aliasing."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_lines as proof
class GroupLinesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-group-lines.json').read_text())
        cls.raw={k:bytes.fromhex(u['hex']) for k,u in cls.spec['units'].items()}
        cls.data=dict(rows=[[0,1,2],[0]],sides=[0,1],lines=[[0,4,0,1,0,1],[1,0,0,65535,0,0],[2,4,0,0,0,0]],limit=3)
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s.replace('maxHeartbeats 4000000','maxHeartbeats 100000'))
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw,self.data));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('ordered_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_instruction_bytes_rejected(self):
        for offset in [4,17,18,19,22,24,27,29,32]:
            with self.subTest(offset=offset):
                raw=self.raw.copy();b=bytearray(raw['group']);b[offset]^=1;raw['group']=bytes(b)
                r=self.lean(proof.certificate(raw,self.data));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_contracts_and_ordering(self):
        s=proof.certificate(self.raw,self.data)
        for old,new in [('(layout : SectorAddresses a n)','(layout : True)'),('(valid : InRange e n)','(valid : True)'),
            ('(inside : i<n)','(inside : True)'),('(sector : s.regs 5=a.sector i)','(sector : True)'),
            ('(line : s.regs 1=a.line e.index)','(line : True)'),('(frontRead : front s=a.sector e.front)','(frontRead : True)'),
            ('(backRead : back s=backAddress e a)','(backRead : True)'),('[0x2e682,0x2e6a2,0x2e6af] 11','[0x2e682,0x2e6a2,0x2e6af] 10')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
        for row in [[2,1,0],[0,1,2,2],[0,2]]:
            data=copy.deepcopy(self.data);data['rows'][0]=row
            r=self.lean(proof.certificate(self.raw,data));self.assertNotEqual(r.returncode,0);self.assertIn('false',r.stdout)
    def test_extraction_mapping_and_relocations(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),self.raw)
        for field,value in [('code_offset','0x2e662'),('file_offset','0x70676'),('hex','90'),('relocations',[])]:
            with self.subTest(field=field):
                spec=copy.deepcopy(self.spec);spec['units']['group'][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_self_edges_null_back_and_aliased_publication(self):
        r=self.lean((ROOT/'tests/reference/original-group-lines.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

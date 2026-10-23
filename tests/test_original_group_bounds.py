"""Kernel proofs, source identity and alias-sensitive bounding-box continuation."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_group_bounds as proof
class GroupBoundsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-group-bounds.json').read_text())
        cls.raw={k:bytes.fromhex(u['hex']) for k,u in cls.spec['units'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('joined_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_bytes_rejected(self):
        for name,offset in [('box',4),('box',8),('box',30),('first',10),('second',12),('second',14),('advance',5),('advance',8),('advance',11)]:
            with self.subTest(name=name,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_wrong_entry_and_fuel_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('exits 38','exits 37'),('⟨s,f,0x2e682⟩','⟨s,f,0x2e680⟩'),('some (result s)','some (advanced s)')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_extraction_mapping_and_relocations(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),self.raw)
        for unit,field,value in [('box','code_offset','0x241e1'),('first','file_offset','0x70697'),('second','hex','90'),('advance','relocations',[])]:
            with self.subTest(unit=unit,field=field):
                spec=copy.deepcopy(self.spec);spec['units'][unit][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_alias_order_inverted_bounds_and_wrap(self):
        r=self.lean((ROOT/'tests/reference/original-group-bounds.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':unittest.main()

"""Raw side-index copies through original cache writes and loop advance."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_line_load as proof
class LineLoadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-line-load.json').read_text())
        cls.raw={k:bytes.fromhex(u['hex']) for k,u in cls.spec['units'].items()}
        cls.raw['cache']=bytes.fromhex(json.loads((ROOT/'tests/reference/original-line-cache.json').read_text())['units']['cache']['hex'])
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    def test_certificate_and_strict_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('inputs_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_altered_instruction_bytes_rejected(self):
        for name,offset in [('copy',3),('copy',7),('copy',15),('cache',24),('advance',9),('advance',12),('advance',15)]:
            with self.subTest(name=name,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_required_contracts_and_result(self):
        s=proof.certificate(self.raw)
        for old,new in [('(h : Source e s)','(h : True)'),('[0x2e29a,0x2e3c1] 26','[0x2e29a,0x2e3c1] 25'),
            ('⟨s,f,0x2e358⟩','⟨s,f,0x2e368⟩'),('s.regs 1+14','s.regs 1+15'),('e.address+62','e.address+64'),('s.regs 5+1','s.regs 5+2')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
    def test_extraction_mapping_and_relocations(self):
        e=proof.extraction;p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(e.extract(binary,p,self.spec),{n:self.raw[n] for n in ['copy','advance']})
        for name,field,value in [('copy','code_offset','0x2e359'),('copy','file_offset','0x7036d'),('copy','hex','90'),('advance','relocations',[])]:
            with self.subTest(name=name,field=field):
                spec=copy.deepcopy(self.spec);spec['units'][name][field]=value
                with self.assertRaises(ValueError):e.extract(binary,p,spec)
    def test_aliasing_wrapping_and_decoder_fixture(self):
        r=self.lean((ROOT/'tests/reference/original-line-load.lean').read_text());self.assertEqual(r.returncode,0,r.stdout+r.stderr)
    def test_raw_source_separation_and_values_are_required(self):
        s=(ROOT/'Doom/Proofs/E1M1LineLoad.lean').read_text()
        for old,new in [('nextRead : Separate 2 2 (s.regs 1+12) (e.address+22)','nextRead : True'),
            ('copyBase : CopySafe 0x2c118 e.address','copyBase : True'),
            ('frontRead : load16 s.memory (s.regs 1+10)=frontIndex','frontRead : True'),
            ('copyBack : backIndex≠65535 → CopySafe (E1M1NoiseGraph.sideAddress sides backIndex) e.address','copyBack : True')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error',r.stdout)
if __name__=='__main__':unittest.main()

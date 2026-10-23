"""Original opening/neighbor certificates, aliases, arithmetic and joins."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_noise_opening as proof
class NoiseOpeningTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-noise-opening.json').read_text())
        self.raw={k:bytes.fromhex(r['hex']) for k,r in self.spec['units'].items()}
    def lean(self,s):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Check.lean';p.write_text(s)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    def test_certificate_and_audit(self):
        r=self.lean(proof.certificate(self.raw));self.assertEqual(r.returncode,0,r.stdout+r.stderr);proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),r.stdout.replace('Quot.sound','bad._native.ax_1'),r.stdout+'extra',r.stdout.replace('line_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
    def test_code_tampering_rejected(self):
        for name,offset in [('opening',13),('opening',33),('opening',55),('opening',89),('opening',105),('neighbor',3),('neighbor',19),('neighbor',32)]:
            with self.subTest(name=name,offset=offset):
                raw=self.raw.copy();b=bytearray(raw[name]);b[offset]^=1;raw[name]=bytes(b)
                r=self.lean(proof.certificate(raw));self.assertNotEqual(r.returncode,0);self.assertIn('decide',r.stdout)
    def test_missing_return_and_bounds_rejected(self):
        s=proof.certificate(self.raw)
        for old,new in [('(ret : (E1M1NoiseOpening.opened s f).pc=0x26fbb)','(ret : True)'),('[0x2c39f] 2','[0x2c39f] 1'),('n≤55','n≤54')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
    def test_extraction_and_fixups(self):
        p=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,p)
        self.assertEqual(proof.extraction.extract(binary,p,self.spec),self.raw)
        for name in self.raw:
            spec=copy.deepcopy(self.spec);spec['units'][name]['relocations']=[]
            with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
            spec=copy.deepcopy(self.spec);spec['units'][name]['file_offset']='0x0'
            with self.assertRaises(ValueError):proof.extraction.extract(binary,p,spec)
    def test_values_aliases_and_decoder(self):
        s=(ROOT/'tests/reference/original-noise-opening.lean').read_text()
        r=self.lean(s);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for old,new in [('memory 0x2c038=72','memory 0x2c038=96'),('result.core.regs 4=5','result.core.regs 4=1'),
            ('memory 0x2c038=0xffffffff','memory 0x2c038=0'),('aliasNeighbor).core.regs 0=sides','aliasNeighbor).core.regs 0=front'),
            ('negativeSide).core.regs 0=back','negativeSide).core.regs 0=front'),('.addMemory 0 ⟨some 4,none,0,0⟩','.subMemory 0 ⟨some 4,none,0,0⟩')]:
            with self.subTest(change=old):
                self.assertIn(old,s);r=self.lean(s.replace(old,new));self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
if __name__=='__main__':unittest.main()

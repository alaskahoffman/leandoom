"""Original no-drop/return certificate, contract rejection and live-helper checks."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_death_return as proof


class E1M1DeathReturnTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-death-return.json').read_text())
        cls.exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        cls.binary=proof.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,cls.exe)
        cls.raw=proof.extraction.extract(cls.binary,cls.exe,cls.spec)

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'Check.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def reject(self,pairs):
        source=proof.certificate(self.raw)
        for old,new in pairs:
            with self.subTest(change=new):
                self.assertIn(old,source)
                result=self.lean(source.replace(old,new))
                self.assertNotEqual(result.returncode,0,result.stdout+result.stderr)
                self.assertIn('error:',result.stdout)

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','bad._native.ax_1'),
                    result.stdout+'unexpected',result.stdout.replace('joined_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_bytes_dispatch_pops_return_rejected(self):
        for offset in [0,5,6,7,26,27,28,68,69,70,71,72,73]:
            with self.subTest(offset=offset):
                raw=dict(self.raw);data=bytearray(raw['dispatch']);data[offset]^=1;raw['dispatch']=bytes(data)
                result=self.lean(proof.certificate(raw))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('decide',result.stdout)

    def test_initial_player_and_saved_frame_contracts_required(self):
        self.reject([('(kind : load32 s.memory (s.regs 3+88)=0)','(kind : True)'),
                     ('(h : E1M1DeathReturn.Inputs s rng)','(h : True)'),
                     ('(outside : (DeathReturn.result s).pc < 0x2a40d ∨ 0x2a457 ≤ (DeathReturn.result s).pc)','(outside : True)')])

    def test_incorrect_restoration_or_return_rejected(self):
        self.reject([('core.regs 4=s.regs 4+24','core.regs 4=s.regs 4+20'),
                     ('core.regs 3=load32 s.memory (s.regs 4+16)','core.regs 3=load32 s.memory (s.regs 4+12)'),
                     ('core.regs 2=s.regs 2','core.regs 2=0'),
                     ('.pc=0x2a6b1','.pc=0x2a6b2'),
                     ('[0x2a6b1] 26','[0x2a6b1] 24')])

    def test_extraction_mapping_and_fixups_required(self):
        for field,value in [('file_offset','0x0'),('code_offset','0x2a40e'),
                            ('relocations',[{'offset':0,'object':3,'target':'0x0'}])]:
            bad=copy.deepcopy(self.spec);bad['units']['dispatch'][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,bad)

    def test_short_unsigned_branch_decoder(self):
        result=self.lean((ROOT/'tests/reference/x86-jb-immediate.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout,'')

    def test_compiled_player_timing_no_drop(self):
        previous=proof.previous
        raw=previous.extract(self.binary,self.exe,json.loads((ROOT/'tests/reference/original-death-timing.json').read_text()))
        corpus=proof.cases()
        with tempfile.TemporaryDirectory() as d:
            inp,out=Path(d)/'input',Path(d)/'output'
            inp.write_text(''.join(f'{tics} {play} {misc}\n' for tics,play,misc,_,_ in corpus))
            subprocess.run([str(ROOT/'.lake/build/bin/death-probe'),'death-return',str(inp),str(out)],check=True)
            expected=[f'{tics-(raw["table"][(play+1)%256]&3)} {(play+1)%256} {misc} 1'
                      for tics,play,misc,_,_ in corpus]
            self.assertEqual(out.read_text().splitlines(),expected)


if __name__=='__main__':unittest.main()

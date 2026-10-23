"""Continuous lethal-floor return, saved-frame provenance, and boundary tests."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_floor_return as proof


class E1M1FloorReturnTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec=json.loads((ROOT/'tests/reference/original-lethal-return.json').read_text())
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
        result=self.lean(proof.certificate(self.raw));self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','bad._native.ax_1'),
                    result.stdout+'unexpected',result.stdout.replace('joined_execution_tracked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_modified_jump_cleanup_pops_and_ret_rejected(self):
        for name,offset in [('jump',1),('epilogue',2),('epilogue',3),('epilogue',4),('epilogue',5),('epilogue',6)]:
            with self.subTest(unit=name,offset=offset):
                raw=dict(self.raw);data=bytearray(raw[name]);data[offset]^=1;raw[name]=bytes(data)
                result=self.lean(proof.certificate(raw));self.assertNotEqual(result.returncode,0);self.assertIn('decide',result.stdout)

    def test_initial_contracts_required(self):
        self.reject([('(ins : E1M1FloorReturn.Inputs s)','(ins : True)'),
                     ('(timing : E1M1DeathTiming.Inputs s sim.rng)','(timing : True)'),
                     ('(dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)','(dead : True)')])

    def test_incorrect_restoration_and_continuation_rejected(self):
        self.reject([('t.pc=pc+5','t.pc=pc+4'),('t.core.regs 4=s.regs 4','t.core.regs 4=s.regs 4+4'),
                     ('t.core.regs 5=s.regs 5','t.core.regs 5=s.regs 6'),('k.core.regs 4=s.regs 4-28','k.core.regs 4=s.regs 4-24')])

    def test_local_bound_and_entry_required(self):
        self.reject([('[(LethalReturn.result s).pc] 6','[(LethalReturn.result s).pc] 5'),
                     ('⟨s,f,0x2a6b1⟩','⟨s,f,0x2a747⟩')])

    def test_extraction_mapping_and_fixups(self):
        for name,field,value in [('jump','file_offset','0x0'),('epilogue','code_offset','0x2a748'),
                                ('epilogue','relocations',[{'offset':0,'object':3,'target':'0x0'}])]:
            bad=copy.deepcopy(self.spec);bad['units'][name][field]=value
            with self.assertRaises(ValueError):proof.extraction.extract(self.binary,self.exe,bad)

    def test_new_separation_contracts_have_witnesses(self):
        result=self.lean((ROOT/'tests/reference/e1m1-floor-return-separation.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr);self.assertEqual(result.stdout,'')

    def test_memory_frame_transport_and_slot_separation(self):
        source='''import Doom.Proofs.DeathStack
open Doom.Proofs Doom.Verification X86 X86Memory
example (sp : Word) (a : Fin 32) : Apart (sp-BitVec.ofNat 32 (4*a.val)) (sp-BitVec.ofNat 32 (4*a.val)) := by
  exact DeathStack.slots_apart sp a a (by decide)
'''
        result=self.lean(source);self.assertNotEqual(result.returncode,0);self.assertIn('error:',result.stdout)


if __name__=='__main__':unittest.main()

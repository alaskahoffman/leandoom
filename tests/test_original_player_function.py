"""Whole P_MovePlayer binary certificates and stack-boundary regressions."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_function as proof

class OriginalPlayerFunctionTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-function.json').read_text())
        self.raw={name:bytes.fromhex(unit['hex']) for name,unit in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Function.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupted_save_scratch_restore_return_rejected(self):
        for offset,value in [(0,0x51),(8,8),(256,8),(257,0x5f),(263,0x90)]:
            with self.subTest(offset=offset):
                changed=dict(self.raw);code=bytearray(changed['playerFunctionBytes']);code[offset]=value
                changed['playerFunctionBytes']=bytes(code)
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_function_entry_derives_body_and_animation_inputs(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerFunction
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerFunction.Inputs s b a c) : PlayerJoined.Inputs (PlayerFunction.enter s) b a c :=
  PlayerFunction.establishes_body s b a c h
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerFunction.Inputs s b a c) : PlayerAnimation.EngineInputs
      (motionEnd (PlayerFunction.enter s) b c).core a c :=
  PlayerJoined.establishes_animation _ b a c (PlayerFunction.establishes_body s b a c h)
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_cannot_omit_prologue_preservation(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerFunction
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerJoined.Inputs (PlayerFunction.frameView s) b a c) :
    PlayerJoined.Inputs (PlayerFunction.enter s) b a c :=
  PlayerFunction.establishes_body s b a c h
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_actual_return_and_saved_register_contract(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerFunction
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerFunction.Inputs s b a c) :
    (PlayerFunction.result s b c).pc = (load32 s.memory (s.regs 4)).toNat :=
  PlayerFunction.result_return s b a c h
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerFunction.Inputs s b a c) :
    PlayerFunction.preservedRegisters (PlayerFunction.result s b c).core =
      (s.regs 3,s.regs 1,s.regs 2,s.regs 6,s.regs 7,s.regs 5,s.regs 4+(4#32)) :=
  PlayerFunction.result_registers s b a c h
example : BlockSummary.Apart ((0#32)-(4#32)) ((0#32)-(8#32)) :=
  PlayerFunction.slots_apart 0 1 2 (by decide)
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_immediate_decoder_signed_values_and_rejected_memory_writes(self):
        result=self.lean('''import Doom.Verification.X86Routine
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open Doom.Verification
example : ∀ r : Fin 8, ∀ v : Fin 256,
    X86Routine.decode [0x83,UInt8.ofNat (0xc0+r.val),UInt8.ofNat v.val] =
      some (.addImmediate r ((BitVec.ofNat 8 v.val).signExtend 32),[]) := by decide
example : ∀ r : Fin 8, ∀ v : Fin 256,
    X86Routine.decode [0x83,UInt8.ofNat (0xe8+r.val),UInt8.ofNat v.val] =
      some (.addImmediate r (-((BitVec.ofNat 8 v.val).signExtend 32)),[]) := by decide
example : X86Routine.decode [0x83,0x04,0x24,0x04] = none := by decide
example : X86Routine.decode [0x83,0x2c,0x24,0x04] = none := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_whole_function_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.joined.original.extract(archive,sw,profile)
        self.assertEqual(proof.joined.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(len(self.raw['playerFunctionBytes']),264)
        for unit in self.spec['units']:
            for index in range(len(self.spec['units'][unit]['relocations'])):
                changed=json.loads(json.dumps(self.spec));changed['units'][unit]['relocations'].pop(index)
                with self.assertRaisesRegex(ValueError,'relocation'):proof.joined.extraction.extract(binary,profile,changed)

if __name__=='__main__':unittest.main()

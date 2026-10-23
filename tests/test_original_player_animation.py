"""Original caller/callee certificates, stack semantics, and runtime connection."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_animation as proof

class OriginalPlayerAnimationTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-animation.json').read_text())
        self.raw={name:bytes.fromhex(unit['hex']) for name,unit in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Animation.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupted_command_state_call_and_return_rejected(self):
        for unit,offset,value in [('playerAnimationBytes',4,5),('playerAnimationBytes',23,151),
                                  ('playerAnimationBytes',28,0x43),('setMobjStateBytes',89,0x59)]:
            with self.subTest(unit=unit,offset=offset):
                changed=dict(self.raw);code=bytearray(changed[unit]);code[offset]=value;changed[unit]=bytes(code)
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_call_and_return_use_stack_memory(self):
        result=self.lean('''import Doom.Verification.X86Routine
open Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
open Doom.Verification.X86Routine
-- CALL's input PC has already advanced past the instruction.
def core : X86Memory.State := ⟨fun r => if r = 4 then 256 else 123,fun _ => 0⟩
def called := X86Routine.execute (.call (-10)) ⟨core,none,21⟩
example : called.map (fun s => (s.pc,s.core.regs 4,load32 s.core.memory 252)) =
    some (11,252,21) := by decide
example : (called.bind (fun s => X86Routine.execute .ret s)).map (fun s => (s.pc,s.core.regs 4)) =
    some (21,256) := by decide
-- A changed return word changes RET's destination; no hardcoded caller return.
def altered : X86Control.State := ⟨⟨core.regs,store32 core.memory 256 99⟩,none,0⟩
example : (X86Routine.execute .ret altered).map (·.pc) = some 99 := by decide
example : X86Routine.execute (.call (-22)) ⟨core,none,21⟩ = none := by decide
example : X86Routine.execute (.call 0) ⟨core,none,4294967296⟩ = none := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_stack_wrap_and_push_esp(self):
        result=self.lean('''import Doom.Verification.X86Routine
open Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
open Doom.Verification.X86Routine
def core : X86Memory.State := ⟨fun _ => 0,fun _ => 0xff⟩
def pushed := X86Routine.execute (.push 4) ⟨core,none,0⟩
example : pushed.map (fun s => (s.core.regs 4,load32 s.core.memory 0xfffffffc)) =
    some (0xfffffffc,0) := by decide
example : (pushed.bind (X86Routine.execute (.pop 0))).map (fun s => (s.core.regs 0,s.core.regs 4)) =
    some (0,0) := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_unsupported_action_and_nonmemory_cmp_fail_closed(self):
        result=self.lean('''import Doom.Verification.X86Routine
open Doom.Verification.X86Routine
example : decode [0xff,0x52,0x0c] = none := by decide
example : decode [0x80,0xff,0] = none := by decide
example : decode [0xe8,0,0,0] = none := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_runtime_helper_is_original_condition(self):
        result=self.lean('''import Doom.PlayerAnim
open Doom
example (s : PlayerAnim.State) (c : Ticcmd) :
    s.startWalking c = (if s.frame == 149 && (c.forwardMove != 0 || c.sideMove != 0)
      then (PlayerAnim.enter 150).1 else s) := by rfl
example : (PlayerAnim.State.mk 149 (-1)).startWalking {sideMove := -128} = ⟨150,4⟩ := by rfl
example : (PlayerAnim.State.mk 156 2).startWalking {forwardMove := 127} = ⟨156,2⟩ := by rfl
example : (PlayerAnim.State.mk 149 (-1)).startWalking {} = ⟨149,-1⟩ := by rfl
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_call_relation_is_derived_from_suffix_entry(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerAnimation
open Doom.Proofs.PlayerAnimation Doom.Verification
example (s : X86Memory.State) (h : Inputs s) : SetterInputs (callCore s) := call_establishes_setter s h
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_extraction_relocations_and_table_identity(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.original.extract(archive,sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(proof.table_data(binary,profile,self.spec).hex(),self.spec['run1']['hex'])
        for unit in self.spec['units']:
            changed=json.loads(json.dumps(self.spec));changed['units'][unit]['relocations']=[]
            with self.assertRaisesRegex(ValueError,'relocation'):proof.extraction.extract(binary,profile,changed)
        changed=json.loads(json.dumps(self.spec));changed['run1']['hex']='00'*28
        with self.assertRaisesRegex(ValueError,'table mismatch'):proof.table_data(binary,profile,changed)

if __name__=='__main__':unittest.main()

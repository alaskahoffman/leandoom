"""Joined region certificates, initial relations, and bounded path composition."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_move_join as proof


class OriginalMoveJoinTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-move-join.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['moveJoinBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Join.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupted_turn_pointer_thrust_and_branch_rejected(self):
        for offset,value in [(8,3),(119,0x48),(135,76)]:
            with self.subTest(offset=offset):
                changed=bytearray(self.raw);changed[offset]=value
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('is false',result.stdout)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_initial_relation_establishes_both_branch_inputs(self):
        result=self.lean('''import Doom.Proofs.OriginalMoveJoin
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
example (s : X86Memory.State) (b : Motion) (c : Ticcmd) (h : MoveJoinInputs s b c) :
    ForwardSideInputs (moveEntryEnd s).core (b.turn c.angleTurn) c :=
  entry_establishes_forward_side s b c h
example (s : X86Memory.State) (b : Motion) (c : Ticcmd) (h : MoveJoinInputs s b c) :
    ThrustTables (moveEntryResultMemory s b c) := entry_tables s b c h
example (s : X86Memory.State) (flags : Option Flags) :
    ∃ k, k ≤ 17 ∧ Prefix moveEntryProgram [48,120] k ⟨s,flags,0⟩ (moveEntryEnd s) ∧
      (moveEntryEnd s).pc ∈ [48,120] := runProgram_path (move_entry_full s flags)
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_path_budget_and_early_exit(self):
        result=self.lean('''import Doom.Verification.X86Paths
open Doom.Verification Doom.Verification.X86Control
-- One instruction is required; extra fuel must not execute past the exit.
def p : Program := fun pc => if pc = 0 then some (.andEax 0,1) else none
def s : State := ⟨⟨fun _ => 123,fun _ => 0⟩,none,0⟩
example : runProgram p [1] 0 s = none := by rfl
example : (runProgram p [1] 1 s).map (·.pc) = some 1 := by decide
example : (runProgram p [1] 50 s).map (·.pc) = some 1 := by decide
example : (runProgram p [0,1] 1 s).map (·.pc) = some 0 := by decide
example (p : Program) (exits : List Nat) (n : Nat) (s t : State)
    (h : runProgram p exits n s = some t) : runProgram p exits (n+100) s = some t :=
  runProgram_mono h 100
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_false_path_cannot_skip_required_step(self):
        result=self.lean('''import Doom.Verification.X86Paths
open Doom.Verification.X86Control
example (p : Program) (s t : State) (h : Prefix p [] 1 s t) : Prefix p [] 0 s t := by
  exact h
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_contiguous_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.original.extract(archive,sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec)['moveJoinBytes'],self.raw)
        self.assertEqual(len(self.raw),136)
        for index in range(4):
            changed=json.loads(json.dumps(self.spec));changed['units']['moveJoinBytes']['relocations'].pop(index)
            with self.assertRaisesRegex(ValueError,'relocation'):proof.extraction.extract(binary,profile,changed)


if __name__=='__main__':unittest.main()

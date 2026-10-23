"""Complete motion certificates and side-thrust seam regressions."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_move_motion as proof


class OriginalMoveMotionTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-move-motion.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['moveMotionBytes']['hex'])

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

    def test_corrupted_branch_side_angle_command_and_store_rejected(self):
        for offset,value in [(135,76),(145,0x20),(156,0xfa),(212,0x48)]:
            with self.subTest(offset=offset):
                changed=bytearray(self.raw);changed[offset]=value
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('is false',result.stdout)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_initial_relation_establishes_both_branch_inputs(self):
        result=self.lean('''import Doom.Proofs.OriginalMoveMotion
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
example (s : X86Memory.State) (b : Motion) (c : Ticcmd) (h : MoveMotionInputs s b c) :
    InlineThrustInputs (sideEntry s b c) (forwardMotion b c) true c.sideMove :=
  motion_establishes_side s b c h
example (s : X86Memory.State) (b : Motion) (c : Ticcmd) (h : MoveMotionInputs s b c) :
    ThrustTables (moveJoinResultMemory s b c) := joined_tables s b c h
example (s : X86Memory.State) (flags : Option Flags) :
    ∃ k, k ≤ 17 ∧ Prefix moveEntryProgram [48,120] k ⟨s,flags,0⟩ (moveEntryEnd s) ∧
      (moveEntryEnd s).pc ∈ [48,120] := runProgram_path (move_entry_full s flags)
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_actual_engine_projection_includes_both_commands(self):
        result=self.lean('''import Doom.Proofs.OriginalMoveMotion
open Doom Doom.Proofs
example (b : Motion) (c : Ticcmd) :
    ((b.movePlayer c).angle,(b.movePlayer c).momx,(b.movePlayer c).momy) =
    ((completeMotion b c).angle,(completeMotion b c).momx,(completeMotion b c).momy) :=
  completeMotion_engine_projection b c
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_cannot_omit_side_table_preservation_obligations(self):
        result=self.lean('''import Doom.Proofs.OriginalMoveMotion
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (c : Ticcmd) (h : MoveJoinInputs s b c) :
    InlineThrustInputs (sideEntry s b c) (forwardMotion b c) true c.sideMove := by
  exact motion_establishes_side s b c h
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_contiguous_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.original.extract(archive,sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec)['moveMotionBytes'],self.raw)
        self.assertEqual(len(self.raw),213)
        for index in range(6):
            changed=json.loads(json.dumps(self.spec));changed['units']['moveMotionBytes']['relocations'].pop(index)
            with self.assertRaisesRegex(ValueError,'relocation'):proof.extraction.extract(binary,profile,changed)


if __name__=='__main__':unittest.main()

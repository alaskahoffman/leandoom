"""Single-relation movement/animation correspondence certificates."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_joined as proof

class OriginalPlayerJoinedTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-joined.json').read_text())
        self.raw={name:bytes.fromhex(unit['hex']) for name,unit in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Joined.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupted_motion_animation_call_and_callee_rejected(self):
        for unit,offset,value in [('playerJoinedBytes',8,3),('playerJoinedBytes',212,0x48),
                                  ('playerJoinedBytes',241,0x43),('setMobjStateBytes',89,0x59)]:
            with self.subTest(unit=unit,offset=offset):
                changed=dict(self.raw);code=bytearray(changed[unit]);code[offset]=value;changed[unit]=bytes(code)
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_initial_relation_derives_actual_animation_input(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerJoined
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerJoined.Inputs s b a c) : PlayerAnimation.EngineInputs (motionEnd s b c).core a c :=
  PlayerJoined.establishes_animation s b a c h
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerJoined.Inputs s b a c) : PlayerAnimation.SetterInputs
      (PlayerAnimation.callCore (motionEnd s b c).core) :=
  PlayerAnimation.call_establishes_setter _ (PlayerJoined.establishes_animation s b a c h).toInputs
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_cannot_omit_animation_preservation_obligations(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerJoined
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : MoveMotionInputs s b c) : PlayerAnimation.EngineInputs (motionEnd s b c).core a c := by
  exact PlayerJoined.establishes_animation s b a c h
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_final_motion_survives_real_animation_writes(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerJoined
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
example (s : X86Memory.State) (flags : Option Flags) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerJoined.Inputs s b a c) :
    (load32 (PlayerAnimation.result (motionEnd s b c).core).core.memory (entryAngleAddress s),
     load32 (PlayerAnimation.result (motionEnd s b c).core).core.memory (entryObject s+(72#32)),
     load32 (PlayerAnimation.result (motionEnd s b c).core).core.memory (entryObject s+(76#32))) =
    ((b.movePlayer c).angle.raw.toBitVec,(b.movePlayer c).momx.raw.toBitVec,(b.movePlayer c).momy.raw.toBitVec) :=
  PlayerJoined.final_motion_fields s flags b a c h
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_contiguous_caller_extraction_and_all_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.original.extract(archive,sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(len(self.raw['playerJoinedBytes']),245)
        self.assertEqual(len(self.raw['setMobjStateBytes']),91)
        for unit in self.spec['units']:
            for index in range(len(self.spec['units'][unit]['relocations'])):
                changed=json.loads(json.dumps(self.spec));changed['units'][unit]['relocations'].pop(index)
                with self.assertRaisesRegex(ValueError,'relocation'):proof.extraction.extract(binary,profile,changed)

if __name__=='__main__':unittest.main()

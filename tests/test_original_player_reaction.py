"""Original reaction gate, caller composition and live player preparation."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_reaction as proof

class OriginalPlayerReactionTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-reaction.json').read_text())
        self.raw={name:bytes.fromhex(unit['hex']) for name,unit in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Reaction.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupted_guard_decrement_store_and_jump_rejected(self):
        for offset,value in [(7,0x75),(8,7),(11,0xfe),(14,0x78),(16,6)]:
            with self.subTest(offset=offset):
                changed=dict(self.raw);code=bytearray(changed['playerReactionBytes']);code[offset]=value
                changed['playerReactionBytes']=bytes(code)
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_guard_derives_caller_and_timer_observation(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerReaction
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd) (timer : Int32)
    (h : PlayerReactionProof.Inputs s b a c timer) : PlayerCaller.Inputs (PlayerReactionProof.guardCore s) b a c :=
  PlayerReactionProof.establishes_caller s b a c timer h
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd) (timer : Int32)
    (h : PlayerReactionProof.Inputs s b a c timer) :
    load32 (PlayerReactionProof.result s b c).core.memory (PlayerReactionProof.timerAddress s) =
      (PlayerReaction.remaining timer).toBitVec := PlayerReactionProof.timer_result s b a c timer h
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_cannot_omit_timer_relation_and_preservation(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerReaction
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd) (timer : Int32)
    (h : PlayerCaller.Inputs s b a c) :
    load32 (PlayerReactionProof.result s b c).core.memory (PlayerReactionProof.timerAddress s) =
      (PlayerReaction.remaining timer).toBitVec := PlayerReactionProof.timer_result s b a c timer h
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_signed_short_jump_decoder_and_bounds(self):
        result=self.lean('''import Doom.Verification.X86Routine
set_option maxRecDepth 32768
open Doom.Verification
example : ∀ v : Fin 256, X86Routine.decode [0xeb,UInt8.ofNat v.val] =
    some (.jump (BitVec.ofNat 8 v.val).toInt,[]) := by decide
example (s : X86Memory.State) : X86Routine.execute (.jump (-3)) ⟨s,none,2⟩ = none := by rfl
example (s : X86Memory.State) : X86Routine.execute (.jump 1) ⟨s,none,4294967295⟩ = none := by rfl
example (s : X86Memory.State) : X86Routine.execute (.jump (-2)) ⟨s,none,2⟩ = some ⟨s,none,0⟩ := by rfl
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_runtime_timer_edges_and_zero_compatibility(self):
        timers=[1,2,-1,-2147483648,2147483647,0]
        args='1234 1000 0 0 50 -40 100 -200 149 -1'
        answers=[list(map(int,line.split())) for line in proof.joined.thrust.probe([f'player-reaction {t} {args}' for t in timers]+[f'player-step {args}'])]
        for t,answer in zip(timers,answers):
            if t:
                remaining=(t-1+2**31)%2**32-2**31
                self.assertEqual(answer,[1234,100,-200,149,-1,remaining])
        self.assertEqual(answers[-2],answers[-1]+[0])

    def test_live_prepare_tick_waits_before_moving_and_animating(self):
        result=self.lean((ROOT/'tests/reference/player-reaction-runtime.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'Except.ok true')

    def test_original_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.joined.original.extract(archive,sw,profile)
        self.assertEqual(proof.joined.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(len(self.raw['playerReactionBytes']),26)
        for unit in self.spec['units']:
            for index in range(len(self.spec['units'][unit]['relocations'])):
                changed=json.loads(json.dumps(self.spec));changed['units'][unit]['relocations'].pop(index)
                with self.assertRaisesRegex(ValueError,'relocation'):proof.joined.extraction.extract(binary,profile,changed)

if __name__=='__main__':unittest.main()

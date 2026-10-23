"""Original height blocks, trust boundary, decoder and runtime edge cases."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_height as proof

class OriginalPlayerHeightTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-height.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Height.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupt_branch_clamp_increment_and_overwrite_rejected(self):
        # JLE -> JG; lower clamp constant; delta increment; airborne jump target.
        for at,value in [(194,0x7f),(218,0x15),(246,0x80),(126,0xa3)]:
            changed=dict(self.raw);code=bytearray(changed['calcHeightBytes']);code[at]=value
            self.assertNotEqual(bytes(code),changed['calcHeightBytes'])
            changed['calcHeightBytes']=bytes(code)
            result=self.lean(proof.certificate(changed,'mutation'))
            self.assertNotEqual(result.returncode,0)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_function_stack_and_control_mutations_rejected(self):
        # First PUSH, no-momentum mask, grounding branch, early clamp branch,
        # live-state branch, first POP and final RET.
        for at,value in [(0,0x52),(70,8),(80,0x74),(110,0x7c),(175,0x74),(295,0x5e),(301,0x90)]:
            changed=dict(self.raw);code=bytearray(changed['calcHeightBytes']);code[at]=value
            self.assertNotEqual(bytes(code),changed['calcHeightBytes'])
            changed['calcHeightBytes']=bytes(code)
            result=self.lean(proof.certificate(changed,'function mutation'))
            self.assertNotEqual(result.returncode,0)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_function_requires_stack_and_return_contracts(self):
        source='''import Doom.Proofs.OriginalHeightFunction
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs.BlockSummary
open Doom.Proofs.PlayerHeight Doom.Proofs.PlayerHeight.Function
example (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    Inputs s body v time ground live :=
  { context := h.context, words := h.words, aliases := h.aliases,
    pushesSafe := h.pushesSafe, savedSafe := h.savedSafe, returnOutside := h.returnOutside }
'''
        for field in ['pushesSafe','savedSafe','returnOutside']:
            # Rebuilding the complete contract without each required field fails.
            changed=source.replace(field+' := h.'+field+', ','').replace(', '+field+' := h.'+field,'')
            self.assertNotEqual(source,changed)
            result=self.lean(changed)
            self.assertNotEqual(result.returncode,0)
            self.assertIn(field,result.stdout)
            self.assertIn('missing',result.stdout.lower())

    def test_height_call_and_join_source_mutations_rejected(self):
        for key,at,value in [('calcHeightCallerBytes',0,0xe9),
                             ('calcHeightCallerBytes',1,0x61),
                             ('playerReactionBytes',6,0x75),
                             ('playerFunctionBytes',0,0x52),
                             ('setMobjStateBytes',0,0x52)]:
            changed=dict(self.raw);code=bytearray(changed[key]);code[at]=value
            self.assertNotEqual(bytes(code),changed[key]);changed[key]=bytes(code)
            result=self.lean(proof.certificate(changed,'caller/join mutation'))
            self.assertNotEqual(result.returncode,0)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_height_caller_requires_memory_separation_but_no_saved_return(self):
        source='''import Doom.Proofs.OriginalHeightCaller
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs.BlockSummary
open Doom.Proofs.PlayerHeight Doom.Proofs.PlayerHeight.Caller
example (s : X86Memory.State) (body : Motion) (v : ViewState)
    (time : Int32) (ground live : Bool) (h : Inputs s body v time ground live) :
    Inputs s body v time ground live :=
  { context := h.context, words := h.words, aliases := h.aliases,
    callSafe := h.callSafe, pushesSafe := h.pushesSafe, savedSafe := h.savedSafe }
example (s : X86Memory.State) : load32 (entry s).memory ((entry s).regs 4) = 0x3a0 :=
  entry_return s
'''
        result=self.lean(source)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for field in ['callSafe','pushesSafe','savedSafe']:
            changed=source.replace(field+' := h.'+field+', ','').replace(', '+field+' := h.'+field,'')
            result=self.lean(changed)
            self.assertNotEqual(result.returncode,0)
            self.assertIn(field,result.stdout)
            self.assertIn('missing',result.stdout.lower())

    def test_join_requires_initial_read_and_ground_protection(self):
        source='''import Doom.Proofs.OriginalPlayerHeightJoin
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs.PlayerHeightJoin
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (timer : Int32) (v : ViewState) (time : Int32) (cached live : Bool)
    (h : Inputs s b a c timer v time cached live) : Inputs s b a c timer v time cached live :=
  { reaction := h.reaction, height := h.height, readsSafe := h.readsSafe,
    groundSafe := h.groundSafe, groundTimer := h.groundTimer }
'''
        result=self.lean(source)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for field in ['readsSafe','groundSafe','groundTimer']:
            changed=source.replace(field+' := h.'+field+', ','').replace(', '+field+' := h.'+field,'')
            result=self.lean(changed)
            self.assertNotEqual(result.returncode,0)
            self.assertIn(field,result.stdout)
            self.assertIn('missing',result.stdout.lower())

    def test_ground_bridge_uses_predecrement_timer(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerGround
open Doom Doom.Proofs.PlayerGround
example : ground { z := ⟨0⟩, floorz := ⟨0⟩ } 0 false = true := by decide
example : ground { z := ⟨1⟩, floorz := ⟨0⟩ } 0 true = false := by decide
example : ground { z := ⟨0⟩, floorz := ⟨0⟩ } 1 false = false := by decide
example : ground { z := ⟨1⟩, floorz := ⟨0⟩ } (-2147483648) true = true := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_shared_origin_call_return_and_body_boundary(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerPreparation
set_option maxRecDepth 32768
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs.PlayerHeight
example : program 301 = none := by decide
example : Function.program 301 = some (.ret,1) := by decide
example : Shared.program 0x3315d = some (.ret,1) := by decide
example : Shared.program 0x333cb = some (.call (-928),5) := by decide
example : Doom.Proofs.PlayerPreparation.program 0x333c4 = some (.call (-617),5) := by decide
example (s : X86Memory.State) : load32 (Shared.entry s).memory ((Shared.entry s).regs 4) = 0x333d0 :=
  Shared.entry_return s
example (s : X86Memory.State) : load32 (Shared.entry s).memory ((Shared.entry s).regs 4) ≠ 0x3a0 := by
  rw [Shared.entry_return]; decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_continuous_certificate_rejects_old_address_convention(self):
        source=proof.certificate(self.raw,'address mutation')
        correct='[0x333d0] 225 ⟨s,flags,0x333b1⟩'
        self.assertEqual(source.count(correct),3)
        for wrong in ['[0x3a0] 225 ⟨s,flags,0x333b1⟩','[0x333d0] 225 ⟨s,flags,0x39b⟩']:
            result=self.lean(source.replace(correct,wrong))
            self.assertNotEqual(result.returncode,0)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_prepared_state_projection_has_distinct_field_offsets(self):
        result=self.lean('''import Doom.Proofs.OriginalPreparedRuntime
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs
set_option maxRecDepth 32768
def fieldMemory : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32
    (store32 (store32 (store32 (store32 (store32 (fun _ => 0)
    (0x1000+32) 1) (0x1000+72) 2) (0x1000+76) 3) (0x1000+100) 4)
    (0x1000+96) 5) (0x1000+124) 6) (0x2000+20) 7) (0x2000+24) 8)
    (0x2000+16) 9) (0x2000+28) 10) 0x2cf90 42
example : PreparedState.read 0x2000 0x1000 fieldMemory =
    ⟨1,2,3,4,5,6,7,8,9,10,true⟩ := by decide
example : (PreparedState.read 0x2000 0x1000 (store32 fieldMemory 0x2cf90 0)).grounded = false := by decide
example : (PreparedState.read 0x2000 0x1000 (store32 fieldMemory 0x2cf90 (-1))).grounded = true := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_full_preparation_certificate_rejects_each_wrong_field(self):
        source=proof.certificate(self.raw,'field mutation')
        expected='Doom.Proofs.PreparedState.expected body anim cmd timer v time cached live'
        target='some (0x333d0,'+expected+',s.regs 4)'
        self.assertEqual(source.count(target),1)
        for field in ['angle','momx','momy','animation','animationTics','reaction',
                      'height','delta','z','bob','grounded']:
            value=('!('+expected+').grounded' if field=='grounded' else '('+expected+').'+field+'+1')
            wrong='some (0x333d0,{ '+expected+' with '+field+' := '+value+' },s.regs 4)'
            result=self.lean(source.replace(target,wrong))
            self.assertNotEqual(result.returncode,0,field)
            self.assertIn('mismatch',result.stdout.lower(),result.stdout)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_live_runtime_connection_requires_successful_supported_scene(self):
        source='''import Doom.Proofs.OriginalPreparedRuntime
open Doom Doom.Collision Doom.Proofs
example (m : Map) (p : Player) (keys : UInt32) (cmd : Ticcmd)
    (scene : Scene) (actor : SolidThing)
    (sync : p.syncScene m = .ok scene) (found : scene.things[0]? = some actor)
    (supported : actor.moveFlags.floating = false) :
    (p.prepareTick m keys (some cmd)).map (fun result => PreparedRuntime.words result.1) =
      .ok (PreparedState.expected (actor.motion p.body) p.animation cmd p.reactionTime
        p.view p.levelTime p.cachedOnGround true) := by
  exact PreparedRuntime.prepare m p keys cmd scene actor sync found supported
'''
        result=self.lean(source)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for premise in ['sync','found','supported']:
            changed=source.replace('scene actor sync found supported',
                'scene actor '+ ' '.join('_' if v==premise else v for v in ['sync','found','supported']))
            result=self.lean(changed)
            self.assertNotEqual(result.returncode,0,premise)
            self.assertIn('placeholder',result.stdout.lower(),result.stdout)

    def test_preparation_matrix_crosses_timer_ground_and_animation(self):
        import verify_original_player_preparation as preparation
        cases=preparation.cases(proof.cases())
        self.assertEqual(len(cases),52052)
        self.assertTrue(any(c[0]==1 and c[3]<=c[4] and c[15]==0 for c in cases))
        self.assertTrue(any(c[0]==-2147483648 and c[3]>c[4] and c[15]==1 for c in cases))
        self.assertTrue(any(c[0]==0 and c[10]==149 and (c[6] or c[7]) for c in cases))

    def test_live_preparation_preserves_cached_ground_on_timer_one(self):
        # Same position and command: a timer of one decrements to zero, but
        # movement and ground refresh must still be skipped on this tic.
        commands=['player-preparation '+c for c in [
            '1 0 0 0 0 8388608 1 0 131072 0 149 -1 2686976 0 1 0 0 1',
            '0 0 0 0 0 8388608 1 0 131072 0 149 -1 2686976 0 1 0 0 1']]
        a,b=[list(map(int,line.split())) for line in proof.joined.thrust.probe(commands)]
        self.assertEqual(a[:6],[0,131072,0,149,-1,0])
        self.assertEqual(a[-1],0)
        self.assertEqual(b[3:6],[150,4,0])
        self.assertNotEqual(a[1:3],b[1:3])
        self.assertEqual(b[-1],1)

    def test_bob_instruction_mutations_rejected(self):
        # FixedMul shift, quarter shift, cap branch, tic multiplier, index mask,
        # sign correction and final FixedMul shift.
        for at,value in [(19,15),(45,1),(55,0x7f),(138,1),(144,1),(159,30),(169,15)]:
            changed=dict(self.raw);code=bytearray(changed['calcHeightBytes']);code[at]=value
            self.assertNotEqual(bytes(code),changed['calcHeightBytes'])
            changed['calcHeightBytes']=bytes(code)
            result=self.lean(proof.certificate(changed,'bob mutation'))
            self.assertNotEqual(result.returncode,0)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_bob_signed_rounding_wrap_and_index_boundaries(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerBob
open Doom Doom.Proofs.PlayerHeight
example : ((-3#32).sshiftRight 2) = (-1#32) := by decide
example : ((-3#32)-(-3#32).sshiftRight 31).sshiftRight 1 = (-1#32) := by decide
example : ((-3#32).sshiftRight 1) ≠ (-1#32) := by decide
example : ((-2147483648#32)-(-2147483648#32).sshiftRight 31).sshiftRight 1 = (-1073741824#32) := by decide
example : (ViewState.bobAmplitude ⟨8388608⟩ ⟨8388608⟩).raw = -536870912 := by decide
example : (ViewState.bobAmplitude ⟨1048576⟩ ⟨0⟩).raw = 1048576 := by decide
example : (ViewState.bobIndex (-1)).val = 7783 := by decide
example : (ViewState.bobIndex (-2147483648)).val = 0 := by decide
example : (ViewState.bobIndex 2147483647).val = 7783 := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_offset_requires_initialized_table(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerBob
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control Doom.Proofs.PlayerHeight
example (s : X86Memory.State) (f : Option Flags) (bob : Fixed) (time : Int32)
    (ht : load32 s.memory 184192 = time.toBitVec)
    (hb : load32 s.memory (s.regs 1+(28#32)) = bob.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [170] 10 ⟨s,f,130⟩).map (fun t =>
      (t.pc,t.core.regs 0,t.core.regs 1,t.core.regs 4,t.core.memory)) =
      some (170,(ViewState.bobOffset bob time).raw.toBitVec,s.regs 1,s.regs 4,s.memory) :=
  offset_observation s f bob time ht hb
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_no_omitted_live_entry_premise(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerHeight
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control Doom.Proofs.PlayerHeight
example (s : X86Memory.State) (f : Option Flags) (v : ViewState)
    (hh : load32 s.memory (s.regs 1+(20#32)) = v.height.raw.toBitVec)
    (hd : load32 s.memory (s.regs 1+(24#32)) = v.delta.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [263] 30 ⟨s,f,177⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(20#32)),load32 t.core.memory (s.regs 1+(24#32)),t.core.regs 0,t.core.regs 1,t.core.regs 4)) =
      some (263,v.recoverHeight.height.raw.toBitVec,v.recoverHeight.delta.raw.toBitVec,s.regs 0,s.regs 1,s.regs 4) :=
  recovery_observation s f v hh hd
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_no_omitted_alias_premise(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerHeight
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control Doom.Proofs.PlayerHeight
example (s : X86Memory.State) (f : Option Flags) (b : Motion) (height offset : Fixed)
    (hz : load32 s.memory (viewObject s+(20#32)) = b.z.raw.toBitVec)
    (hh : load32 s.memory (s.regs 1+(20#32)) = height.raw.toBitVec)
    (hc : load32 s.memory (viewObject s+(60#32)) = b.ceilingz.raw.toBitVec)
    (ho : s.regs 0 = offset.raw.toBitVec) :
    (X86Routine.run (X86Routine.decodeAt code) [295] 12 ⟨s,f,263⟩).map (fun t =>
      (t.pc,load32 t.core.memory (s.regs 1+(16#32)),t.core.regs 1,t.core.regs 4)) =
      some (295,(ViewState.clampZ b height offset).raw.toBitVec,s.regs 1,s.regs 4) :=
  ceiling_observation s f b height offset hz hh hc ho
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_decoder_signed_branches_shift_and_unsupported_inputs(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerHeight
open Doom.Verification
example : X86Routine.decode [0xe9,0xfe,0xff,0xff,0xff] = some (.jump (-2),[]) := by decide
example : X86Routine.decode [0x81,0xfa,0,0,0x10,0] = some (.compareRegister 2 1048576,[]) := by decide
example : X86Routine.decode [0x7d,0x80] = some (.jumpSigned 0 (-128),[]) := by decide
example : X86Routine.decode [0x66,0xd1,0xf8] = none := by decide
example : X86Routine.decode [0xc7,0xc0,1,0,0,0] = none := by decide
example : X86Routine.decode [0xf6,0xc0,4] = none := by decide
example : X86Routine.decode [0x69,0x05,0,0,0,0] = none := by decide
example : X86Routine.decode [0xc1,0xfa,2] = some (.sar 2 2,[]) := by decide
example (s : X86Memory.State) (f : Option X86Control.Flags) :
    X86Routine.execute (.sar 0 32) ⟨s,f,0⟩ = some ⟨X86Memory.put s 0 (s.regs 0),f,0⟩ := by simp [X86Routine.execute]
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 0 1) ⟨s,none,0⟩ = none := by rfl
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 0 1) ⟨s,some ⟨false,false,false,none⟩,4294967295⟩ = none := by rfl
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_live_height_extremes_and_unclamped_airborne_view(self):
        cases=[
            ('2686976 -16384 0 8388608 0 0 0 1 0 1',[2670592,1,2670592,0]),
            ('100 0 0 8388608 0 0 0 1 0 1',[1343488,16385,1343488,0]),
            ('2686977 0 0 8388608 0 0 0 1 0 1',[2686976,0,2686976,0]),
            ('6553600 0 0 3276800 0 0 0 0 0 1',[6553600,0,6553600,0]),
            ('6553600 0 0 3276800 0 0 0 1 1 1',[6553600,0,6553600,0]),
            ('2686976 0 0 1966080 0 0 0 1 0 0',[2686976,0,1703936,0]),
        ]
        answers=[list(map(int,line.split())) for line in proof.joined.thrust.probe(['calc-height '+c for c,_ in cases])]
        self.assertEqual(answers,[answer for _,answer in cases])

    def test_full_routine_case_matrix(self):
        cases=proof.cases()
        self.assertEqual(len(cases),50132)
        self.assertEqual({(c[6]*409)&8191 for c in cases[:16384]},set(range(8192)))
        self.assertTrue(any(c[1]==-16384 for c in cases))
        self.assertTrue(any(-2147483648 in c[:7] for c in cases))

    def test_original_extraction_and_all_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.joined.original.extract(archive,sw,profile)
        self.assertEqual(proof.joined.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual(len(self.raw['calcHeightBytes']),302)
        for index in range(3):
            changed=json.loads(json.dumps(self.spec));changed['units']['calcHeightBytes']['relocations'].pop(index)
            with self.assertRaisesRegex(ValueError,'relocation'):proof.joined.extraction.extract(binary,profile,changed)

if __name__=='__main__':unittest.main()

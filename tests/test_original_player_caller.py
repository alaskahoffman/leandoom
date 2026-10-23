"""Original caller/callee composition, return-address derivation and argument reload."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_player_caller as proof

class OriginalPlayerCallerTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-player-caller.json').read_text())
        self.raw={name:bytes.fromhex(unit['hex']) for name,unit in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Caller.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_corrupted_argument_call_target_and_reload_rejected(self):
        for offset,value in [(1,0xc8),(3,0x98),(6,0),(8,0xc8)]:
            with self.subTest(offset=offset):
                changed=dict(self.raw);code=bytearray(changed['playerCallerBytes']);code[offset]=value
                changed['playerCallerBytes']=bytes(code)
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_caller_derives_full_function_entry(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerCaller
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerCaller.Inputs s b a c) : PlayerFunction.Inputs (PlayerCaller.callEntry s) b a c :=
  PlayerCaller.establishes_function s b a c h
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerCaller.Inputs s b a c) : PlayerJoined.Inputs
      (PlayerFunction.enter (PlayerCaller.callEntry s)) b a c :=
  PlayerFunction.establishes_body _ b a c (PlayerCaller.establishes_function s b a c h)
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_cannot_omit_call_stack_preservation(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerCaller
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerJoined.Inputs (PlayerCaller.layout s) b a c) :
    PlayerFunction.Inputs (PlayerCaller.callEntry s) b a c :=
  PlayerCaller.establishes_function s b a c h
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_return_address_is_written_without_a_premise(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerCaller
open Doom Doom.Proofs Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control
example (s : X86Memory.State) : load32 (PlayerCaller.callEntry s).memory
    ((PlayerCaller.callEntry s).regs 4) = 0x333c9 := PlayerCaller.entry_return s
example (s : X86Memory.State) (flags : Option Flags) :
    X86Routine.Prefix PlayerCaller.program [0x333cb] 2 ⟨s,flags,0x333c2⟩
      ⟨PlayerCaller.callEntry s,flags,0x33160⟩ := PlayerCaller.call_prefix s flags
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_stack_and_player_argument_restored_for_next_call(self):
        result=self.lean('''import Doom.Proofs.OriginalPlayerCaller
open Doom Doom.Proofs Doom.Verification
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerCaller.Inputs s b a c) :
    PlayerFunction.preservedRegisters (PlayerCaller.result s b c).core =
      PlayerFunction.preservedRegisters s := PlayerCaller.result_registers s b a c h
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd)
    (h : PlayerCaller.Inputs s b a c) : (PlayerCaller.result s b c).core.regs 0 = s.regs 2 :=
  PlayerCaller.result_argument s b a c h
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_original_caller_function_extraction_and_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.joined.original.extract(archive,sw,profile)
        self.assertEqual(proof.joined.extraction.extract(binary,profile,self.spec),self.raw)
        self.assertEqual([len(self.raw[k]) for k in ['playerCallerBytes','playerFunctionBytes','setMobjStateBytes']],[9,264,91])
        for unit in self.spec['units']:
            for index in range(len(self.spec['units'][unit]['relocations'])):
                changed=json.loads(json.dumps(self.spec));changed['units'][unit]['relocations'].pop(index)
                with self.assertRaisesRegex(ValueError,'relocation'):proof.joined.extraction.extract(binary,profile,changed)

if __name__=='__main__':unittest.main()

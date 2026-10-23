"""Continuous forward thrust / side guard certificate and linear bridge tests."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_forward_side as proof


class OriginalForwardSideTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-forward-side.json').read_text())
        self.raw=bytes.fromhex(self.spec['units']['forwardSideBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'ForwardSide.lean';p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'\nextra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_changed_momentum_side_register_and_branch_rejected(self):
        for offset,value in [(71,0x48),(73,0x56),(87,76)]:
            with self.subTest(offset=offset):
                changed=bytearray(self.raw);changed[offset]=value
                result=self.lean(proof.certificate(changed,'mutation'))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('is false',result.stdout)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_linear_bridge_and_boundary_rejection(self):
        result=self.lean('''import Doom.Proofs.OriginalForwardSide
open Doom.Verification Doom.Verification.X86 Doom.Verification.X86Memory
open Doom.Verification.X86Control
-- The linear bridge retains the same byte decoder, including lengths.
example : decodePackets 1 [0x89,0xc1] = some [(.legacy (.mov 1 0),2)] := by decide
example : decodePackets 1 [0x89] = none := by decide
example : decodePackets 0 [0x89,0xc1] = none := by decide
example : decodePackets 1 [0x74,0] = none := by decide
-- Static fit obligations reject an altered opcode or an early exit.
def p : Program := fun pc => if pc = 0 then some (.block (.legacy (.mov 1 0)),2) else none
example : LinearFits p [2] 0 [(.legacy (.mov 1 0),2)] := by decide
example : ¬ LinearFits p [0,2] 0 [(.legacy (.mov 1 0),2)] := by decide
example : ¬ LinearFits p [2] 0 [(.legacy (.mov 2 0),2)] := by decide
example : ¬ LinearFits p [2] 0 [(.legacy (.mov 1 0),3)] := by decide
example (s : X86Control.State) :
    (linearEnd [(.legacy (.mov 1 0),2)] s).flags = s.flags := by rfl
example (s : X86Control.State) :
    (linearEnd [(.legacy (.shl 0 16),3)] s).flags = none := by rfl
example (s : X86Memory.State) (flags : Option Flags) :
    runProgram (decodeAt Doom.Proofs.forwardSideBytes) [88,165] 28 ⟨s,flags,0⟩ =
    runProgram (decodeAt Doom.Proofs.forwardSideBytes) [88,165] 5
      ⟨Doom.Proofs.forwardEnd s,none,72⟩ := (Doom.Proofs.forward_linear_prefix s flags).run 5
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_false_preservation_rejected(self):
        # The guard reads after momentum writes; separation cannot be silently dropped.
        result=self.lean('''import Doom.Proofs.OriginalForwardSide
open Doom.Verification.X86Memory
example (m : Memory) (a : Word) : load32 (store32 m a 0) a = load32 m a := by
  exact Doom.Proofs.BlockSummary.load_store m a 0
''')
        self.assertNotEqual(result.returncode,0)
        self.assertIn('mismatch',result.stdout.lower())

    def test_original_extraction_and_all_relocations(self):
        profile=json.loads((ROOT/'tests/reference'/self.spec['exe_profile']).read_text())
        sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        archive=ROOT/sw['local_directory']/'doom19s.zip'
        if not archive.exists():self.skipTest('shareware archive not installed')
        binary=proof.original.extract(archive,sw,profile)
        self.assertEqual(proof.extraction.extract(binary,profile,self.spec)['forwardSideBytes'],self.raw)
        changed=json.loads(json.dumps(self.spec));changed['units']['forwardSideBytes']['relocations'].pop()
        with self.assertRaisesRegex(ValueError,'relocation'):proof.extraction.extract(binary,profile,changed)


if __name__=='__main__':unittest.main()

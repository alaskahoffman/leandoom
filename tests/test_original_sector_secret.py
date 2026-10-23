"""Original secret-sector case: writes, precise frame, return and trust boundary."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_sector_secret as proof

class SectorSecretTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-sector-secret.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}

    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Secret.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'extra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_counter_offset_width_value_pop_and_ret_mutations_rejected(self):
        for at,value in [(1,0x8e),(2,0xd8),(6,0x67),(9,0x10),(10,1),(12,0x5f),(16,0x90)]:
            changed=dict(self.raw);code=bytearray(changed['sectorSecretBytes'])
            self.assertNotEqual(code[at],value)
            code[at]=value;changed['sectorSecretBytes']=bytes(code)
            result=self.lean(proof.certificate(changed,'mutation'))
            self.assertNotEqual(result.returncode,0,at)
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_half_store_preserves_neighbors_and_wraps(self):
        result=self.lean('''import Doom.Proofs.OriginalSectorSecret
open Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Routine
example : load32 (store16 (fun _ => 0xa5) 0xffffffff 0) 0xffffffff = 0xa5a50000 := by decide
example : store16 (fun _ => 0xa5) 0xffffffff 0 1 = 0xa5 := by decide
example : store16 (fun _ => 0xa5) 0xffffffff 0 0xfffffffe = 0xa5 := by decide
example : load16 (store16 (fun _ => 0xa5) 0xffffffff 0xabcd) 0xffffffff = 0xabcd := by decide
example : X86Routine.decode [0x66,0xc7,0x41,0x0e,0x34,0x12] =
    some (.storeHalfImmediate ⟨some 1,none,0,14⟩ 0x1234,[]) := by decide
example : X86Routine.decode [0x66,0xc7,0x41,0x0e,0x34] = none := by decide
example : X86Routine.decode [0x66,0xc7,0xc0,0,0] = none := by decide
example : X86Routine.decode [0xff,0x8e,0xd4,0,0,0] = none := by decide
example : X86Routine.decode [0xff,0xd0] = none := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_live_secret_counter_wrap_and_floor_gate(self):
        result=self.lean('''import Doom.Proofs.OriginalSectorSecret
open Doom
example : (LevelSpecials.secret 9 ⟨0⟩ ⟨0⟩ 2147483647) = (0,-2147483648) := by decide
example : (LevelSpecials.secret 9 ⟨0⟩ ⟨0⟩ (-1)) = (0,0) := by decide
example : (LevelSpecials.secret 9 ⟨1⟩ ⟨0⟩ 7) = (9,7) := by decide
example : (LevelSpecials.secret 0 ⟨0⟩ ⟨0⟩ 7) = (0,7) := by decide
example : (LevelSpecials.secret 9 ⟨0⟩ ⟨0⟩ 7) = (0,8) := by decide
example : (LevelSpecials.secret 0 ⟨0⟩ ⟨0⟩ 8) = (0,8) := by decide
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_return_requires_protected_stack_and_external_target(self):
        source='''import Doom.Proofs.OriginalSectorSecret
open Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control Doom.Proofs.SectorSecret
example (s : X86Memory.State) (flags : Option Flags)
    (safe : StackSafe s) (outside : 17 ≤ returnPc s) :
    X86Routine.run program [returnPc s] 7 ⟨s,flags,0⟩ = some ⟨final s,none,returnPc s⟩ := by
  exact execution s flags safe outside
'''
        result=self.lean(source);self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for wrong in ['execution s flags _ outside','execution s flags safe _']:
            result=self.lean(source.replace('execution s flags safe outside',wrong))
            self.assertNotEqual(result.returncode,0)
            self.assertIn('placeholder',result.stdout.lower())

    def test_runtime_relation_requires_secret_floor_and_nonaliasing(self):
        source=proof.certificate(self.raw,'premise test')
        correct='observation s flags n z floor onFloor isSecret encoded separate safe outside'
        for field in ['onFloor','isSecret','encoded','separate']:
            wrong=' '.join('_' if word==field else word for word in correct.split())
            result=self.lean(source.replace(correct,wrong))
            self.assertNotEqual(result.returncode,0,field)
            self.assertIn('placeholder',result.stdout.lower())
            with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_case_matrix_covers_overflow_and_unaligned_layouts(self):
        cases=proof.cases()
        self.assertEqual(len(cases),16708)
        self.assertTrue(any(n==2147483647 for n,z,a in cases))
        self.assertEqual({a for n,z,a in cases},{0,1,2,3})
        self.assertTrue(any(n==-1 and z==-2147483648 for n,z,a in cases))

if __name__=='__main__':unittest.main()

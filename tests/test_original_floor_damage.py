"""Original floor bytes, proof trust boundary, real memory contracts and decoder."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_floor_damage as proof

class OriginalFloorDamageTests(unittest.TestCase):
    def setUp(self):
        self.spec=json.loads((ROOT/'tests/reference/original-floor-damage.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}
        self.raw['randomTableBytes']=bytes.fromhex(json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())['units']['randomTableBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Floor.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0],result.stdout+'extra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_damage_clock_suit_threshold_call_rng_and_table_mutations_rejected(self):
        mutations=[('floorDamageBytes',at) for at in [2,17,25,30,71,91,127]]
        mutations += [('playRandomBytes',at) for at in [1,5,7,18,27]]
        mutations += [('randomTableBytes',60)]
        for name,at in mutations:
            with self.subTest(unit=name,offset=at):
                bad=dict(self.raw);raw=bytearray(bad[name]);raw[at]^=1;bad[name]=bytes(raw)
                result=self.lean(proof.certificate(bad,'mutation'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_on_floor_and_initial_memory_contract_cannot_be_dropped(self):
        source=proof.certificate(self.raw,'premises')
        correct='correspondence kind s flags time suit rng z floor onFloor h'
        for wrong in [correct.replace('onFloor','_'),correct[:-1]+'_']:
            result=self.lean(source.replace(correct,wrong))
            self.assertNotEqual(result.returncode,0)
            self.assertIn('placeholder',result.stdout.lower())

    def test_concrete_contract_witnesses_wrap_and_rng_on_no_damage_tic(self):
        result=self.lean((ROOT/'tests/reference/floor-damage.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_extended_decoder_and_unknown_flags_fail_closed(self):
        result=self.lean('''import Doom.Proofs.OriginalFloorDamage
open Doom.Verification Doom.Verification.X86Routine Doom.Verification.X86Memory Doom.Verification.X86Control
example : X86Routine.decode [0x83,0xf8,0xff] = some (.compareRegister 0 0xffffffff,[]) := by decide
example : X86Routine.decode [0x0f,0x8d,0xff,0xff,0xff,0xff] = some (.jumpSigned 0 (-1),[]) := by decide
example : X86Routine.decode [0x31,0xdb] = some (.xorRegister 3 3,[]) := by decide
example : X86Routine.decode [0x31,0x1b] = none := by decide
example : X86Routine.decode [0xa1,0x20,0x27,1,0] = some (.control (.block (.load 0 ⟨none,none,0,0x12720⟩)),[]) := by decide
example : X86Routine.decode [0xa1,0x20,0x27,1] = none := by decide
example : X86Routine.decode [0x0f,0x8d,0x7b,0,0] = none := by decide
example : X86Routine.decode [0x83,0xf8] = none := by decide
example (s : X86Memory.State) : X86Routine.execute (.jumpSigned 0 2) ⟨s,none,0⟩ = none := rfl
example (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.execute (.addImmediate 0 1) ⟨s,f,0⟩).map (·.flags) = some none := rfl
example (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.execute (.xorRegister 2 2) ⟨s,f,0⟩).map (fun t => t.core.regs 2) = some 0 := by
  simp [X86Routine.execute,put,Doom.Verification.X86.write]
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_crosscheck_matrix_includes_every_clock_residue_and_seed(self):
        cases=proof.cases()
        self.assertEqual({t%32 for _,_,t,_,_ in cases},set(range(32)))
        self.assertEqual({i for _,_,_,i,_ in cases},set(range(256)))
        self.assertEqual({z for _,_,_,_,z in cases},{-1,0,1})
        self.assertTrue(any(s==-1 for _,s,_,_,_ in cases))
        self.assertTrue(any(t>2**30 for _,_,t,_,_ in cases))

if __name__=='__main__':unittest.main()

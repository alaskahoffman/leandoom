"""Original sector dispatch: byte binding, word width, contracts and proof audit."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_sector_dispatch as proof

class SectorDispatchTests(unittest.TestCase):
    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/original-sector-dispatch.json').read_text())
        self.raw = {k: bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}

    def lean(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'Sector.lean'
            path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def test_certificate_and_strict_audit(self):
        result = self.lean(proof.certificate(self.raw, 'test'))
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound', 'sorryAx'),
                    result.stdout.replace('Quot.sound', 'unchecked._native.bv_decide.ax_1'),
                    result.stdout.splitlines()[0], result.stdout+'extra']:
            with self.assertRaises(ValueError):
                proof.audit(bad)

    def test_corrupted_pointer_width_branch_argument_and_call_rejected(self):
        for at, value in [(4,0x38), (7,0x67), (10,0x10), (12,0x75),
                          (13,0x06), (15,0xc0), (17,0x3c)]:
            changed = dict(self.raw)
            code = bytearray(changed['sectorDispatchBytes'])
            self.assertNotEqual(code[at], value)
            code[at] = value
            changed['sectorDispatchBytes'] = bytes(code)
            result = self.lean(proof.certificate(changed, 'mutation'))
            self.assertNotEqual(result.returncode, 0, at)
            with self.assertRaises(ValueError):
                proof.audit(result.stdout)

    def test_cmp16_flags_sign_extension_and_fail_closed_decoder(self):
        result = self.lean('''import Doom.Proofs.OriginalSectorDispatch
open Doom.Verification Doom.Verification.X86Routine
example : (compare16 0 0).zero = true := by decide
example : (compare16 0x8000 0).sign = true := by decide
example : (compare16 0x8000 0).overflow = false := by decide
example : compare16 0x7fff 0xffff = ⟨false,true,true,none⟩ := by decide
example : compare16 0x8000 1 = ⟨false,false,true,none⟩ := by decide
example : compare16 0 0xffff = ⟨false,false,false,none⟩ := by decide
example : decode [0x66,0x83,0x78,0x0e,0xff] =
    some (.compareHalf ⟨some 0,none,0,14⟩ 0xffff,[]) := by decide
example : decode [0x66,0x83,0x78,0x0e] = none := by decide
example : decode [0x66,0x83,0xc0,1] = none := by decide
example : decode [0x66,0x83,0xf8,1] = some (.compareHalfRegister 0 1,[]) := by decide
example : decode [0x66,0x81,0x78,0x0e,0,0] = none := by decide
''')
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_special_is_halfword_and_wraps_at_address_boundary(self):
        result = self.lean('''import Doom.Proofs.OriginalSectorDispatch
open Doom.Verification Doom.Verification.X86Memory Doom.Proofs.SectorDispatch
example : load16 (store32 (fun _ => 0xa5) 0xffffffff 0xa5a50000) 0xffffffff = 0 := by decide
example : load16 (store32 (fun _ => 0xa5) 0xffffffff 0xa5a58000) 0xffffffff = 0x8000 := by decide
example : exitPc 0 = 0x333e5 := by decide
example : exitPc 0x8000 = 0x333e0 := by decide
example : exitPc 0xffff = 0x333e0 := by decide
example : program 0x333e0 = some (.call (-14533),5) := by decide
example : program 0x333e5 = none := by decide
''')
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_join_requires_protected_initial_sector_reads(self):
        source = '''import Doom.Proofs.OriginalSectorDispatch
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs
example (s t : X86Memory.State) (edx : t.regs 2 = s.regs 2)
    (frame : PlayerHeight.Frame s.memory t.memory (SectorDispatch.writes s))
    (safe : SectorDispatch.Safe s) : SectorDispatch.special t = SectorDispatch.special s := by
  exact SectorDispatch.special_preserved s t edx frame safe
'''
        result = self.lean(source)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        result = self.lean(source.replace('s t edx frame safe', 's t edx frame _'))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('placeholder', result.stdout.lower())

    def test_join_rejects_wrong_branch_and_old_stop(self):
        source = proof.certificate(self.raw, 'bad observation')
        changes = [('SectorDispatch.exitPc (SectorDispatch.special s)', '0x333e5'),
                   ('[0x333e0,0x333e5] 231', '[0x333d0] 231')]
        for old, new in changes:
            self.assertIn(old, source)
            result = self.lean(source.replace(old, new))
            self.assertNotEqual(result.returncode, 0)
            with self.assertRaises(ValueError):
                proof.audit(result.stdout)

if __name__ == '__main__':
    unittest.main()

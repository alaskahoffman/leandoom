"""Original CALL/prologue contract and continuous sector-handler certificate."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_sector_caller as proof

class SectorCallerTests(unittest.TestCase):
    def setUp(self):
        self.spec = json.loads((ROOT/'tests/reference/original-sector-caller.json').read_text())
        self.raw = {k: bytes.fromhex(v['hex']) for k,v in self.spec['units'].items()}

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'Caller.lean'
            path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def test_certificate_and_strict_audit(self):
        r = self.lean(proof.certificate(self.raw, 'test'))
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)
        proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound', 'sorryAx'),
                    r.stdout.replace('Quot.sound', 'unchecked._native.bv_decide.ax_1'),
                    r.stdout.splitlines()[0], r.stdout+'extra']:
            with self.assertRaises(ValueError):
                proof.audit(bad)

    def test_call_target_save_order_and_return_mutations_rejected(self):
        for key, at, value in [('sectorCallerBytes', 12, 0x75),  # reversed zero guard
                               ('sectorCallerBytes', 15, 0xc8),  # wrong argument source
                               ('sectorCallerBytes', 17, 0x3c),  # CALL one byte too far
                               ('sectorEntryBytes', 0, 0x51),   # save ECX instead of EBX
                               ('sectorEntryBytes', 3, 0x57),   # save EDI instead of ESI
                               ('sectorSecretBytes', 12, 0x5f), # restore EDI instead of ESI
                               ('sectorReturnBytes', 4, 0x90),  # missing RET
                               ('sectorTableBytes', 20, 0xdd)]:
            with self.subTest(unit=key, offset=at):
                raw = dict(self.raw)
                code = bytearray(raw[key])
                self.assertNotEqual(code[at], value)
                code[at] = value
                raw[key] = bytes(code)
                r = self.lean(proof.certificate(raw, 'mutation'))
                self.assertNotEqual(r.returncode, 0)
                with self.assertRaises(ValueError):
                    proof.audit(r.stdout)

    def test_initial_contract_requires_stack_separation(self):
        source = '''import Doom.Proofs.OriginalSectorCaller
open Doom Doom.Verification Doom.Proofs.SectorCaller
example (s : X86Memory.State) (z floor : Fixed) (n : Int32) (h : Inputs s z floor n) : Inputs s z floor n :=
  { isSecret := h.isSecret, height := h.height, floor := h.floor, count := h.count,
    separate := h.separate, stackApart := h.stackApart }
'''
        r = self.lean(source)
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)
        for field in ['isSecret', 'height', 'floor', 'count', 'separate', 'stackApart']:
            bad = source.replace(field+' := h.'+field+', ', '').replace(', '+field+' := h.'+field, '')
            r = self.lean(bad)
            self.assertNotEqual(r.returncode, 0, field)
            self.assertIn('missing', r.stdout.lower())

    def test_saved_words_derive_from_call_even_when_stack_wraps(self):
        r = self.lean('''import Doom.Proofs.OriginalSectorCaller
open Doom.Verification Doom.Verification.X86 Doom.Verification.X86Memory Doom.Proofs.SectorCaller
-- ESP=8 means three of the five stores wrap into the top of the address space.
def s : X86Memory.State := ⟨fun r => if r = 4 then 8 else BitVec.ofNat 32 (r.val+100),fun _ => 0xa5⟩
example : load32 (saved s) (4#32) = (0x333e5#32) := by
  have h := congrArg Prod.fst (saved_words s)
  exact h
example : load32 (saved s) (0xfffffff4#32) = (106#32) := by
  have h := saved_words s
  simp only [Prod.mk.injEq] at h
  exact h.2.2.2.2
example : Doom.Proofs.SectorSecret.returnPc (enter s) = 0x333e5 := return_address s
example : preserved (Doom.Proofs.SectorEntry.result (enter s)).core = preserved s := restores s''')
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)

    def test_call_budget_and_actual_return_pc(self):
        r = self.lean('''import Doom.Proofs.OriginalSectorCaller
set_option maxRecDepth 32768
open Doom.Verification Doom.Verification.X86Memory Doom.Verification.X86Control Doom.Proofs
example : SectorCaller.program 0x333e0 = some (.call (-14533),5) := by decide
example (s : X86Memory.State) (f : Option Flags) :
  X86CodeMemory.run (SectorEntry.codeMemory SectorEntry.tableBytes) SectorCaller.program [0x333e5] 0
    ⟨s,f,0x333e0⟩ = none := by rfl
-- The CALL pushes the *following* instruction's PC and uses relative displacement.
example (s : X86Memory.State) (f : Option Flags) :
  X86CodeMemory.execute (SectorEntry.codeMemory SectorEntry.tableBytes) (.call (-14533))
    ⟨s,f,0x333e5⟩ = some ⟨X86Routine.pushWord s 0x333e5,f,0x2fb20⟩ := by
  simp [X86CodeMemory.execute,X86Routine.execute]
''')
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)

if __name__ == '__main__':
    unittest.main()

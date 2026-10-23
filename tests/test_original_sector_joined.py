"""Continuous preparation-to-handler proof and absolute return-address boundary."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_sector_joined as proof

class SectorJoinedTests(unittest.TestCase):
    def setUp(self):
        spec = json.loads((ROOT/'tests/reference/original-sector-joined.json').read_text())
        self.raw = {k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'Joined.lean'; p.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],
                                  cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_axiom_audit(self):
        r = self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        proof.audit(r.stdout)
        for bad in [r.stdout.replace('Quot.sound','sorryAx'),
                    r.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    r.stdout.splitlines()[0],r.stdout+'extra']:
            with self.assertRaises(ValueError): proof.audit(bad)

    def test_mutations_across_both_sides_of_join_rejected(self):
        for key,at in [('playerReactionBytes',0),('playerFunctionBytes',0),('setMobjStateBytes',0),
                       ('calcHeightCallerBytes',1),('calcHeightBytes',0),('sectorDispatchBytes',17),
                       ('sectorEntryBytes',0),('sectorSecretBytes',0),('sectorReturnBytes',4),('sectorTableBytes',20)]:
            with self.subTest(unit=key):
                raw = dict(self.raw); code = bytearray(raw[key]); code[at] ^= 1; raw[key] = bytes(code)
                r = self.lean(proof.certificate(raw,'mutated'))
                self.assertNotEqual(r.returncode,0)
                with self.assertRaises(ValueError): proof.audit(r.stdout)

    def test_initial_contract_requires_both_memory_directions(self):
        source = '''import Doom.Proofs.OriginalSectorJoined
open Doom Doom.Verification Doom.Proofs.SectorJoined
example (s : X86Memory.State) (b : Motion) (a : PlayerAnim.State) (c : Ticcmd) (r : Int32)
    (v : ViewState) (t : Int32) (cached live : Bool) (floor : Fixed) (n : Int32)
    (h : Inputs s b a c r v t cached live floor n) : Inputs s b a c r v t cached live floor n :=
  { preparation := h.preparation, sector := h.sector, sectorReads := h.sectorReads, preparedReads := h.preparedReads }
'''
        r = self.lean(source); self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        for field in ['preparation','sector','sectorReads','preparedReads']:
            bad = source.replace(field+' := h.'+field+', ','').replace(', '+field+' := h.'+field,'')
            r = self.lean(bad); self.assertNotEqual(r.returncode,0,field)
            self.assertIn('missing',r.stdout.lower())

    def test_single_absolute_code_origin_and_real_calls(self):
        r = self.lean('''import Doom.Proofs.OriginalSectorJoined
set_option maxRecDepth 32768
open Doom.Proofs Doom.Verification
example : SectorJoined.program 0x2511 = none := by decide
example : SectorJoined.program 0x333c4 = some (.call (-617),5) := by decide
example : SectorJoined.program 0x333cb = some (.call (-928),5) := by decide
example : SectorJoined.program 0x333e0 = some (.call (-14533),5) := by decide
example (s : X86Memory.State) : X86Memory.load32 (PlayerCaller.callEntry s).memory ((PlayerCaller.callEntry s).regs 4) = 0x333c9 := PlayerCaller.entry_return s
example (s : X86Memory.State) : X86Memory.load32 (PlayerHeight.Shared.entry s).memory ((PlayerHeight.Shared.entry s).regs 4) = 0x333d0 := PlayerHeight.Shared.entry_return s
example (s : X86Memory.State) : SectorSecret.returnPc (SectorCaller.enter s) = 0x333e5 := SectorCaller.return_address s
'''); self.assertEqual(r.returncode,0,r.stdout+r.stderr)

    def test_bridge_requires_routine_semantics(self):
        r = self.lean('''import Doom.Verification.X86CodeBridge
open Doom.Verification
example : X86CodeMemory.routineOnly (.jumpCode ⟨none,none,0,0⟩) = false := by rfl
example (cm : X86Memory.Memory) (s : X86Control.State) :
  X86CodeMemory.execute cm (.call 1) s = X86Routine.execute (.call 1) s :=
    X86CodeMemory.execute_routine cm _ s rfl
'''); self.assertEqual(r.returncode,0,r.stdout+r.stderr)

if __name__ == '__main__': unittest.main()

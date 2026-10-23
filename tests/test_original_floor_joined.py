"""Preparation-to-floor proof, two-way memory contracts, and byte extraction."""
import json
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_floor_joined as proof

class FloorJoinedTests(unittest.TestCase):
    def setUp(self):
        spec=json.loads((ROOT/'tests/reference/original-floor-joined.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}
        self.raw['randomTableBytes']=bytes.fromhex(json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())['units']['randomTableBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Joined.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_certificate_and_strict_axiom_audit(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.bv_decide.ax_1'),
                    result.stdout.replace('FloorJoined.transport','missing'),result.stdout+'extra']:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_mutations_on_both_sides_and_tables_rejected(self):
        mutations=[('playerReactionBytes',0),('playerFunctionBytes',0),('setMobjStateBytes',0),
                   ('calcHeightCallerBytes',1),('calcHeightBytes',0),('sectorCallerBytes',17),
                   ('sectorEntryBytes',0),('floorDamageBytes',91),('playRandomBytes',5),
                   ('sectorTableBytes',48),('randomTableBytes',66)]
        for name,offset in mutations:
            with self.subTest(unit=name):
                raw=dict(self.raw);data=bytearray(raw[name]);data[offset]^=1;raw[name]=bytes(data)
                result=self.lean(proof.certificate(raw,'mutated'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_initial_contract_requires_both_memory_directions_and_table(self):
        source='''import Doom.Proofs.OriginalFloorJoined
open Doom Doom.Verification Doom.Proofs.FloorJoined
example (kind : Doom.Proofs.FloorDamage.Kind) (s : X86Memory.State)
    (body : Motion) (anim : PlayerAnim.State) (cmd : Ticcmd) (timer : Int32)
    (v : ViewState) (time : Int32) (cached live : Bool) (floor : Fixed)
    (tick : Nat) (suit : Bool) (rng : DoomRandom)
    (h : Inputs kind s body anim cmd timer v time cached live floor tick suit rng) :
    Inputs kind s body anim cmd timer v time cached live floor tick suit rng :=
  { preparation := h.preparation, floorInputs := h.floorInputs, floorReads := h.floorReads,
    tableRead := h.tableRead, preparedReads := h.preparedReads }
'''
        result=self.lean(source);self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for field in ['preparation','floorInputs','floorReads','tableRead','preparedReads']:
            bad=re.sub(r'\b'+field+r' := h\.'+field+r',?\s*','',source)
            result=self.lean(bad)
            self.assertNotEqual(result.returncode,0,field)
            self.assertIn('missing',result.stdout.lower())

    def test_absolute_calls_and_both_program_halves(self):
        result=self.lean('''import Doom.Proofs.OriginalFloorJoined
set_option maxRecDepth 32768
open Doom.Proofs Doom.Verification
example : FloorJoined.program 0x333c4 = some (.call (-617),5) := by decide
example : FloorJoined.program 0x333cb = some (.call (-928),5) := by decide
example : FloorJoined.program 0x333e0 = some (.call (-14533),5) := by decide
example : FloorJoined.program 0x2fbb0 = some (.call (-47701),5) := by decide
example : FloorJoined.program 0x2511 = none := by decide
example (pc : Nat) (h : PlayerPreparation.program pc ≠ none) :
    FloorJoined.program pc = PlayerPreparation.program pc := FloorJoined.contains_preparation pc h
example (pc : Nat) (h : FloorCaller.program pc ≠ none) :
    FloorJoined.program pc = FloorCaller.program pc := FloorJoined.contains_caller pc h
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_continuous_lean_runs_keep_prepared_fields_and_floor_results(self):
        result=self.lean((ROOT/'tests/reference/floor-joined.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'['+', '.join(['true']*12)+']')

    def test_comparison_matrix_covers_independent_floor_seams(self):
        inputs,profiles=proof.preparation.floor_cases(proof.height.cases())
        self.assertEqual(len(inputs),len(profiles))
        self.assertEqual({p[2] for p in profiles},set(range(256)))
        for special in [5,7,4,16]:
            for suit in [0,1,-1]:
                for seed in [0,65,255]:
                    for tick in [0,1,32]:
                        for timer in [0,2]:
                            for offset in [0,1]:
                                self.assertTrue(any(p==(special,suit,seed,offset) and c[14]==tick and c[0]==timer
                                                    for c,p in zip(inputs,profiles)))

    def test_probe_accepts_full_natural_clock_and_rejects_bad_word_fields(self):
        good=['damage 0 0 5 0 4294967296 65','damage 0 0 4 1 4294967297 65',
              'damage 0 0 16 1 18446744073709551616 255']
        self.assertEqual(proof.sector.secret_probe(good),['10 65','0 66','20 0'])
        with self.assertRaises(subprocess.CalledProcessError):
            proof.sector.secret_probe(['damage 2147483648 0 5 0 0 65'])

if __name__=='__main__':unittest.main()

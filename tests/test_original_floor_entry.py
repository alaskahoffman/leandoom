"""Joined floor-contact/switch/decision proof and initial-state contracts."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_floor_damage as proof

class FloorEntryTests(unittest.TestCase):
    def setUp(self):
        spec=json.loads((ROOT/'tests/reference/original-floor-damage.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}
        self.raw['randomTableBytes']=bytes.fromhex(json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())['units']['randomTableBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'Entry.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_joined_certificate_has_no_native_or_missing_audits(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        self.assertIn("'Doom.Proofs.FloorEntry.correspondence' depends on axioms",result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.ax_1'),
                    result.stdout.replace('FloorEntry.case_inputs','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_floor_guard_switch_index_and_each_target_mutations_fail(self):
        mutations=[('sectorEntryBytes',i) for i in [15,16,18,24,26,30,34,41,47,51]]
        mutations += [('sectorTableBytes',i) for i in [0,4,12,48]]
        for name,i in mutations:
            with self.subTest(unit=name,offset=i):
                raw=dict(self.raw);data=bytearray(raw[name]);data[i]^=1;raw[name]=bytes(data)
                result=self.lean(proof.certificate(raw,'mutated entry'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_contract_is_initial_and_field_relations_are_required(self):
        source='''import Doom.Proofs.OriginalFloorEntry
open Doom Doom.Verification Doom.Proofs
open Doom.Proofs.FloorDamage (Kind)
example (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : FloorEntry.Inputs kind s z floor time suit rng) :
    FloorEntry.Inputs kind s z floor time suit rng := by
  exact ⟨h.isKind,h.height,h.floor,h.suit,h.clock,h.index,h.misc,h.random,h.clockSafe,h.targetSafe,h.miscSafe⟩
'''
        result=self.lean(source);self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for field in ['isKind','height','floor','suit','clock','index','misc','random','clockSafe','targetSafe','miscSafe']:
            result=self.lean(source.replace('h.'+field+(',' if field!='miscSafe' else '⟩'),
                                            '_'+(',' if field!='miscSafe' else '⟩')))
            self.assertNotEqual(result.returncode,0,field)
            self.assertIn('placeholder',result.stdout.lower())

    def test_real_joined_runs_high_bits_above_below_floor_and_rng_wrap(self):
        result=self.lean((ROOT/'tests/reference/floor-entry.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'['+', '.join(['true']*12)+']')

    def test_one_less_than_full_bound_can_fail_and_skip_needs_only_seven(self):
        base=(ROOT/'tests/reference/floor-entry.lean').read_text().split('#eval',1)[0]
        result=self.lean(base+'''
#eval [(X86CodeMemory.run FloorEntry.cm FloorEntry.program FloorDamage.exits 30
    ⟨initial .four 0 0 65 1 32,none,0x2fb24⟩).isNone,
  (X86CodeMemory.run FloorEntry.cm FloorEntry.program FloorDamage.exits 7
    ⟨initial .four 1 0 65 1 32,none,0x2fb24⟩).map FloorDamage.observe == some (0,65,173)]
end FloorEntryFixture
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'[true, true]')

if __name__=='__main__':unittest.main()

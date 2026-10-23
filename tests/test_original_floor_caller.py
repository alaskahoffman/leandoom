"""Initial-state CALL/prologue composition through the damaging-floor decision."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_floor_damage as proof

class FloorCallerTests(unittest.TestCase):
    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Caller.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_outer_call_prologue_mutations_rejected(self):
        spec=json.loads((ROOT/'tests/reference/original-floor-damage.json').read_text())
        raw={k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}
        raw['randomTableBytes']=bytes.fromhex(json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())['units']['randomTableBytes']['hex'])
        for name,offset in [('sectorCallerBytes',i) for i in [1,5,10,12,15,16,17]]+ [('sectorEntryBytes',i) for i in range(4)]:
            with self.subTest(unit=name,offset=offset):
                mutated=dict(raw);data=bytearray(raw[name]);data[offset]^=1;mutated[name]=bytes(data)
                result=self.lean(proof.certificate(mutated,'mutated caller'))
                self.assertNotEqual(result.returncode,0)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_wraparound_unaligned_stack_and_concrete_contract_witnesses(self):
        result=self.lean((ROOT/'tests/reference/floor-caller.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'['+', '.join(['true']*12)+']')

    def test_full_path_needs_42_steps_and_off_floor_18(self):
        base=(ROOT/'tests/reference/floor-caller.lean').read_text().split('#eval',1)[0]
        result=self.lean(base+'''
#eval [(X86CodeMemory.run FloorCaller.cm FloorCaller.program FloorDamage.exits 41
    ⟨initial .four 0 0 65 1 32,none,0x333d0⟩).isNone,
  (X86CodeMemory.run FloorCaller.cm FloorCaller.program FloorDamage.exits 18
    ⟨initial .four 1 0 65 1 32,none,0x333d0⟩).map FloorDamage.observe == some (0,65,173)]
end FloorCallerFixture
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'[true, true]')

    def test_initial_fields_and_separation_are_required(self):
        source='''import Doom.Proofs.OriginalFloorCaller
open Doom Doom.Verification Doom.Proofs
open Doom.Proofs.FloorDamage (Kind)
example (kind : Kind) (s : X86Memory.State) (z floor : Fixed) (time : Nat)
    (suit : Bool) (rng : DoomRandom) (h : FloorCaller.Inputs kind s z floor time suit rng) :
    FloorCaller.Inputs kind s z floor time suit rng := by
  exact ⟨h.isKind,h.height,h.floor,h.suit,h.clock,h.index,h.misc,h.table,h.stackSafe,h.tableSafe,h.targetIndexSafe⟩
'''
        result=self.lean(source);self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        for field in ['isKind','height','floor','suit','clock','index','misc','table','stackSafe','tableSafe','targetIndexSafe']:
            result=self.lean(source.replace('h.'+field+(',' if field!='targetIndexSafe' else '⟩'),
                                            '_'+(',' if field!='targetIndexSafe' else '⟩')))
            self.assertNotEqual(result.returncode,0,field)
            self.assertIn('placeholder',result.stdout.lower())

    def test_stack_alias_contract_is_not_vacuous(self):
        base=(ROOT/'tests/reference/floor-caller.lean').read_text().split('-- EDX',1)[0]
        # First PUSH at player: corrupts the object pointer. The checked premise rejects it.
        result=self.lean(base+'''
def aliased : X86Memory.State := X86Memory.put (initial .four 0 0 65 1 32) 4 0x40004
example : ¬ Doom.Proofs.BlockSummary.Apart (aliased.regs 2) (aliased.regs 4-(4#32)) := by
  intro h
  exact h 0 0 (by decide)
example (h : FloorCaller.Inputs .four aliased ⟨0⟩ ⟨0⟩ 32 true ⟨65,173⟩) : False := by
  have overlap := h.stackSafe (aliased.regs 2) (by simp [FloorCaller.reads])
    (aliased.regs 4-(4#32)) (by simp [FloorCaller.slots,SectorCaller.slots])
  exact overlap 0 0 (by decide)
end FloorCallerFixture
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':unittest.main()

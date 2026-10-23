"""Pinned DOS callback suffix, ordered array append and real firing-prefix join."""
import copy
import json
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import verify_original_line_finish as proof
HEADER = '''import Doom.Proofs.E1M1LineFinish
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
'''


class LineFinishTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('error:', result.stdout)
        for failure in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(failure, result.stdout.lower())

    def setUp(self):
        self.spec, self.profile, self.raw = proof.extracted()
        self.source = proof.certificate(self.raw)

    def test_certificate_and_strict_axiom_audit(self):
        out = self.succeeds(self.source)
        proof.audit(out)
        for bad in [out.replace('Quot.sound', 'sorryAx'), out.replace('Quot.sound', 'native.ax'),
                    out + 'extra', out.replace('append_encoded', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)

    def test_byte_and_execution_mutations(self):
        for offset in [0, 4, 22, 31, 38, 63, 69, 72, 82, 94]:
            raw = copy.deepcopy(self.raw)
            code = bytearray(raw['finish']); code[offset] ^= 1; raw['finish'] = code
            with self.subTest(offset=offset):
                self.rejects(proof.certificate(raw))
        for old, new in [('n≤23', 'n≤22'), ('⟨s,f,0x2c6bb⟩', '⟨s,f,0x2c6bc⟩')]:
            self.rejects(self.source.replace(old, new))

    def test_live_decision_needs_encoded_inputs(self):
        source = HEADER + '''open OriginalLineFinish
attribute [local irreducible] result
example (s : X86Memory.State) (frac : Fixed) (line : Collision.Line) (flags : Nat) (p : Word)
    (h : Inputs s frac line flags p) :
    (result s).core.regs 0=(if frac.raw < 0 then (1#32)
      else if flags &&& 4 != 0 && frac.raw < 65536 && line.back.isNone then 0 else 1) :=
  decision_live s frac line flags p h
'''
        self.succeeds(source)
        self.rejects(source.replace('Inputs s frac line flags p', 'True'))
        self.rejects(source.replace('frac.raw < 65536', 'frac.raw ≤ 65536'))

    def test_memory_frame_and_return_need_separation(self):
        source = HEADER + '''open OriginalLineFinish
attribute [local irreducible] result cursor
example (s : X86Memory.State) (a : Word)
    (safe : ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)], Apart a w) :
    load32 (result s).core.memory a=load32 s.memory a := frame s a safe
'''
        self.succeeds(source)
        self.rejects(source.replace('Apart a w', 'True'))
        source = HEADER + '''open OriginalLineFinish
attribute [local irreducible] result cursor
example (s : X86Memory.State)
    (safe : ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)], Apart (s.regs 4+(36#32)) w) :
    (result s).pc=(load32 s.memory (s.regs 4+(36#32))).toNat := returned s safe
'''
        self.succeeds(source)
        self.rejects(source.replace('Apart (s.regs 4+(36#32)) w', 'True'))

    def test_ordered_append_requires_all_contracts(self):
        source = HEADER + '''open OriginalLineFinish
attribute [local irreducible] result cursor Encodes
example (s : X86Memory.State) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (hit : Collision.Intercept)
    (enabled : inserts s) (encoded : Encodes s.memory base resolve hits)
    (atEnd : cursor s=base+BitVec.ofNat 32 (12*hits.size))
    (fraction : s.regs 0=hit.frac.raw.toBitVec) (kind : hit.isLine=true)
    (pointer : s.regs 1=resolve hit)
    (newSafe : ∀ off∈[(0#32),4,8], Apart (cursor s+off) (0x2c028#32))
    (oldSafe : ∀ (i : Nat), i<hits.size → ∀ off∈[(0#32),4,8],
      ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)],
        Apart (base+BitVec.ofNat 32 (12*i)+off) w) :
    Encodes (result s).core.memory base resolve (hits.push hit) :=
  append_encoded s base resolve hits hit enabled encoded atEnd fraction kind pointer newSafe oldSafe
'''
        self.succeeds(source)
        for old in ['inserts s', 'Encodes s.memory base resolve hits',
                    'cursor s=base+BitVec.ofNat 32 (12*hits.size)', 'hit.isLine=true',
                    'Apart (cursor s+off) (0x2c028#32)', 'Apart (base+BitVec.ofNat 32 (12*i)+off) w']:
            with self.subTest(contract=old):
                self.rejects(source.replace(old, 'True'))

    def test_capacity_and_numeric_fixtures(self):
        source = HEADER + '''open OriginalLineFinish
attribute [local irreducible] Collision.appendIntercept
example (r : Collision.PathResult) (hit : Collision.Intercept) (capacity : r.collected.size<128) :
    Collision.appendIntercept r hit=.ok {r with collected:=r.collected.push hit} := append_live r hit capacity
'''
        self.succeeds(source)
        self.rejects(source.replace('r.collected.size<128', 'r.collected.size≤128'))
        source = (ROOT / 'tests/reference/original-line-finish.lean').read_text()
        self.succeeds(source)
        for old, new in [('=(0x60080d#32)', '=(0x600809#32)'), ('regs 4=(25#32)', 'regs 4=(24#32)'),
                         ('regs 5=(123#32)', 'regs 5=(555#32)'), ('some 128', 'some 129'),
                         (').isOk=false', ').isOk=true')]:
            self.assertIn(old, source)
            self.rejects(source.replace(old, new, 1))

    def test_real_firing_join(self):
        source = HEADER + '''open E1M1LineFinish
attribute [local irreducible] finish
example (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (c : Weapon.Context) (h : E1M1DischargeSetters.Inputs gun s c)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (safe : E1M1LineFraction.Ready (E1M1LineSecondPoint.lineTest gun s)) :
    ∃ n≤644, X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (finish gun s) :=
  line_finish_execution gun s f c h ox oy sx sy ex ey geometry layout xout yout okX okY safe
'''
        self.succeeds(source)
        for old, new in [('n≤644', 'n≤643'), ('E1M1LineFraction.Ready (E1M1LineSecondPoint.lineTest gun s)', 'True')]:
            self.rejects(source.replace(old, new))

    def test_original_mapping_and_relocations(self):
        sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
        binary = proof.extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, self.profile)
        self.assertEqual(proof.extraction.extract(binary, self.profile, self.spec), self.raw)
        for key, value in [('file_offset', '0x0'), ('relocations', [])]:
            bad = copy.deepcopy(self.spec); bad['units']['finish'][key] = value
            with self.assertRaises(ValueError):
                proof.extraction.extract(binary, self.profile, bad)


if __name__ == '__main__':
    unittest.main()

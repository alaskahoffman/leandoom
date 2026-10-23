"""Reject malformed map cells and weakened scan-entry/capacity contracts."""
import re
import struct
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map as proof
HEADER = '''import Doom.Proofs.E1M1PathMap
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1PathMap
'''


class PathMapTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMap.lean').read_text()
        declaration = source[source.index('theorem '+name):].split(' := by', 1)[0]
        return HEADER+declaration.replace('theorem '+name, 'example', 1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self, source, changes):
        self.succeeds(source)
        for old, new in changes:
            self.assertIn(old, source)
            with self.subTest(change=old):
                self.rejects(source.replace(old, new))

    def test_map_shape_and_parser_rejects_corruption(self):
        data, _ = proof.pinned_data()
        self.assertEqual(len(data['cells']), 828)
        self.assertEqual(max(map(lambda c: len(c[1]), data['cells'])), 13)
        self.assertEqual(sum(len(ids) for _, ids in data['cells']), 1801)
        self.assertTrue(any(len(ids) != len(set(ids)) for _, ids in data['cells']))
        for addr, value in [(2, 35), (4, 32768), (data['cells'][0][0], 475),
                            (data['cells'][0][0], 1)]:
            words = data['words'].copy()
            words[addr] = value
            with self.assertRaises(ValueError):
                proof.decode_blockmap(struct.pack('<'+'H'*len(words), *words))

    def test_leading_zero_duplicates_and_raw_word_binding(self):
        fixture = HEADER+'''def words : Array Nat := #[0,0,474,65535]
def cell : Cell := ⟨0,[0,0,474]⟩
example : cell.Valid words := by decide
example : #[0] ++ cell.ids.tail.toArray=cell.ids.toArray := live_visits words cell (by decide)
'''
        self.succeeds(fixture)
        for old, new in [('⟨0,[0,0,474]⟩', '⟨0,[0,474]⟩'),
                         ('#[0,0,474,65535]', '#[0,0,474,0]'),
                         ('474', '475')]:
            self.rejects(fixture.replace(old, new))

    def test_sequential_certificate_requires_payload_and_offsets(self):
        self.mutations(self.contract('sequence_valid', 'words start cells encoded checked'), [
            ('(encoded : words.toList.drop start=payload cells)', '(encoded : True)'),
            ('(checked : checkSequence start cells=true)', '(checked : True)')])
        fixture = HEADER+'example : ∀ c∈[Cell.mk 0 [0,0,474],Cell.mk 4 [0]], c.Valid #[0,0,474,65535,0,65535] :=\n  sequence_valid _ 0 _ (by decide) (by decide)\n'
        self.succeeds(fixture)
        self.rejects(fixture.replace('Cell.mk 4', 'Cell.mk 3'))
        self.rejects(fixture.replace('#[0,0,474,65535,0,65535]', '#[0,0,474,65535,0,0]'))

    def test_cell_reserve_is_a_real_bound(self):
        def fixture(n):
            return HEADER+'example : (Cell.mk 0 ['+','.join(['0']*n)+']).Valid #['+','.join(['0']*n+['65535'])+'] := by decide\n'
        self.succeeds(fixture(13))
        self.rejects(fixture(14))

    def test_pointer_needs_image_cursor_and_line_base(self):
        source = self.contract('pointer_from_image', 's base lines words c valid image cursor lineBase i frac')
        self.mutations(source, [
            ('(image : WordImage s.memory base words)', '(image : True)'),
            ('(cursor : s.regs 2=base+BitVec.ofNat 32 (2*c.offset))', '(cursor : True)'),
            ('(lineBase : load32 s.memory 0x2c120=lines)', '(lineBase : True)'),
            ('resolve lines ⟨frac,true,c.ids[i.val]⟩', 'resolve lines ⟨frac,true,c.ids[i.val]+1⟩')])

    def test_sentinel_and_nonlast_require_certified_data(self):
        for name, args in [('sentinel_from_image', 's base words c valid image cursor'),
                           ('nonlast_from_image', 's base words c valid image cursor i')]:
            self.mutations(self.contract(name, args), [('(valid : c.Valid words)', '(valid : True)')])

    def test_capacity_comes_from_original_initialization(self):
        self.mutations(self.contract('initialized_collection', 's ox oy sx sy ex ey h words c valid resolver'), [
            ('(h : OriginalPathInit.Inputs s ox oy sx sy ex ey)', '(h : True)'),
            ('(valid : c.Valid words)', '(valid : True)'),
            ('#[] c.ids.length', '#[] (c.ids.length+129)')])
        self.mutations(self.contract('reserve_cell', 's base resolver hits words c valid tracked'), [
            ('resolver hits 13)', 'resolver hits 0)')])

    def test_strict_audit_and_complete_module_coverage(self):
        source = HEADER+'\n'.join('#print axioms Doom.Proofs.E1M1PathMap.'+n for n in proof.PROOFS)
        output = self.succeeds(source)
        prefix = '\n'.join("'Doom.Verification.ExtractedPathMap."+n+"' does not depend on any axioms" for n in proof.NAMES)+'\n'
        proof.audit(prefix+output)
        for bad in [output.replace('Quot.sound', 'sorryAx'), output+'extra', output.replace('reserve_cell', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(prefix+bad)
        text = (ROOT/'Doom/Proofs/E1M1PathMap.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))


if __name__ == '__main__':
    unittest.main()

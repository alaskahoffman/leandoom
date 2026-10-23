"""Actual original lookup establishes pinned map scan-entry facts."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map_lookup as proof
HEADER = '''import Doom.Proofs.E1M1PathMapLookup
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapLookup
'''
ARGS = 's f base lines words c x y width height context inside valid image selected lineBase'


class PathMapLookupTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMapLookup.lean').read_text()
        declaration = source[source.index('theorem '+name):].split(' := by', 1)[0]
        return HEADER+declaration.replace('theorem '+name, 'example', 1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self, source, changes):
        self.succeeds(source)
        for old, new in changes:
            self.assertIn(old, source)
            with self.subTest(change=old):
                self.rejects(source.replace(old, new))

    def test_certificate_and_complete_strict_audit(self):
        output = self.succeeds(self.source)
        proof.audit(output)
        for bad in [output.replace('Quot.sound', 'sorryAx'), output.replace('Quot.sound', 'native.ax'),
                    output+'extra', output.replace('lookup_preserves_collection', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        source = (ROOT/'Doom/Proofs/E1M1PathMapLookup.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', source, re.M))

    def test_extracted_bytes_entry_and_instruction_count(self):
        raw = copy.deepcopy(self.raw)
        raw['cell'] = bytes([raw['cell'][0] ^ 1])+raw['cell'][1:]
        self.rejects(proof.certificate(self.data, raw))
        self.mutations(self.source, [('[] 8 ⟨s,f,0x2c541⟩', '[] 7 ⟨s,f,0x2c541⟩'),
                                     ('[] 8 ⟨s,f,0x2c541⟩', '[] 8 ⟨s,f,0x2c544⟩')])

    def test_join_needs_pre_lookup_representation(self):
        self.mutations(self.contract('lookup_to_scan', ARGS), [
            ('(context : Context s base x y width)', '(context : True)'),
            ('(image : WordImage s.memory base words)', '(image : True)'),
            ('(selected : words[4+Collision.pathCellIndex x y width]?=some c.offset)', '(selected : True)'),
            ('(lineBase : load32 s.memory 0x2c120=lines)', '(lineBase : True)'),
            ('(valid : c.Valid words)', '(valid : True)')])

    def test_cursor_and_frame_are_conclusions(self):
        args = 's base words c x y width height context inside valid image selected'
        self.mutations(self.contract('lookup_ready', args), [
            ('(2*c.offset) ∧', '(2*c.offset+2) ∧'),
            ('(OriginalLineCell.lookup s).core.regs 4=s.regs 4', '(OriginalLineCell.lookup s).core.regs 4=s.regs 4+4'),
            ('(OriginalLineCell.lookup s).pc=0x2c57f', '(OriginalLineCell.lookup s).pc=0x2c55c')])

    def test_inside_bound_and_table_header(self):
        self.mutations(self.contract('e1m1_index_bound', 'x y inside'), [
            ('(inside : Collision.pathCellInside x y 36 23=true)', '(inside : True)'),
            ('36<828', '36<827')])
        self.mutations(self.contract('table_address', 'base index'), [('base+(8#32)', 'base+(6#32)')])
        self.succeeds(HEADER+'''example : Collision.pathCellIndex 35 22 36=827 := by decide
example : Collision.pathCellInside (-1) 0 36 23=false := by decide
example : Collision.pathCellInside 36 0 36 23=false := by decide
example : Collision.pathCellInside 0 23 36 23=false := by decide
''')

    def test_collection_preserved_without_extra_capacity(self):
        self.mutations(self.contract('lookup_preserves_collection', 's base resolver hits reserve tracked'), [
            ('(tracked : OriginalLineCollection.Tracks s base resolver hits reserve)', '(tracked : True)'),
            ('OriginalLineCollection.Tracks (OriginalLineCell.lookup s).core base resolver hits reserve :=',
             'OriginalLineCollection.Tracks (OriginalLineCell.lookup s).core base resolver hits (reserve+1) :=')])

    def test_wrapping_image_duplicate_zero_and_existing_hit(self):
        fixture = (ROOT/'tests/reference/e1m1-path-map-lookup.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('⟨5,[0,0,474]⟩', '⟨5,[0,474]⟩'),
                         ('(0x2c100,base+8)', '(0x2c100,base+6)'),
                         ('core.regs 2=(5#32)', 'core.regs 2=(7#32)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

"""Bounds entry establishes lookup context and protected scan inputs."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map_bounds as proof
HEADER = '''import Doom.Proofs.E1M1PathMapBounds
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapBounds
'''
ARGS = 's f base lines words c x y w h bounds globals inside valid image safe selected'


class PathMapBoundsTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMapBounds.lean').read_text()
        declaration = source[source.index('theorem '+name):].split(' := by', 1)[0]
        return HEADER+declaration.replace('theorem '+name, 'example', 1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self, source, changes):
        self.succeeds(source)
        for old, new in changes:
            self.assertIn(old, source)
            with self.subTest(change=old):
                self.rejects(source.replace(old, new))

    def test_certificate_and_strict_audit(self):
        output = self.succeeds(self.source)
        proof.audit(output)
        for bad in [output.replace('Quot.sound', 'sorryAx'), output.replace('Quot.sound', 'native.ax'),
                    output+'extra', output.replace('collection_preserved', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1PathMapBounds.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_all_extracted_segments_and_execution_entry(self):
        for key in ['lineEntry', 'lineReturn', 'cell']:
            raw = copy.deepcopy(self.raw)
            raw[key] = bytes([raw[key][0] ^ 1])+raw[key][1:]
            with self.subTest(segment=key):
                self.rejects(proof.certificate(self.data, raw))
        self.mutations(self.contract('inside_to_scan', ARGS), [
            ('⟨s,f,0x2c520⟩', '⟨s,f,0x2c527⟩'), ('∃ n≤24', '∃ n≤0')])

    def test_inside_join_requires_initial_representation_and_safety(self):
        self.mutations(self.contract('inside_to_scan', ARGS), [
            ('(bounds : OriginalLineBounds.Inputs s x y w h)', '(bounds : True)'),
            ('(globals : Globals s base lines)', '(globals : True)'),
            ('(image : WordImage s.memory base words)', '(image : True)'),
            ('(safe : ImageSafe s base words)', '(safe : True)'),
            ('(selected : words[4+Collision.pathCellIndex x y w]?=some c.offset)', '(selected : True)')])

    def test_stack_word_protection_cannot_be_dropped(self):
        self.mutations(self.contract('result_frame', 's a safe'), [('(safe : Safe s a)', '(safe : True)')])
        self.mutations(self.contract('image_preserved', 's base words image safe'), [
            ('(safe : ImageSafe s base words)', '(safe : True)')])

    def test_context_is_derived_and_frame_size_is_exact(self):
        self.mutations(self.contract('lookup_context', 's base lines x y w h bounds globals inside'), [
            ('(inside : Collision.pathCellInside x y w h=true)', '(inside : True)')])
        self.mutations(self.contract('inside_to_scan', ARGS), [
            ('s.regs 4-(8#32)', 's.regs 4-(4#32)'),
            ('(scanStart s).pc=0x2c57f', '(scanStart s).pc=0x2c541')])

    def test_outside_return_has_no_map_image_but_needs_bounds(self):
        self.mutations(self.contract('outside_returns', 's f x y w h bounds outside'), [
            ('(outside : Collision.pathCellInside x y w h=false)', '(outside : True)'),
            ('(bounds : OriginalLineBounds.Inputs s x y w h)', '(bounds : True)'),
            ('s.regs 4+4', 's.regs 4'),
            ('core.regs 0=1', 'core.regs 0=0')])

    def test_collection_requires_only_existing_records_and_cursor_protection(self):
        source = self.contract('collection_preserved', 's base resolver hits reserve tracked cursorSafe recordsSafe')
        self.mutations(source, [
            ('(cursorSafe : Safe s (0x2c028#32))', '(cursorSafe : True)'),
            ('(recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8], Safe s (base+BitVec.ofNat 32 (12*i)+off))', '(recordsSafe : True)'),
            ('OriginalLineCollection.Tracks (scanStart s).core base resolver hits reserve :=',
             'OriginalLineCollection.Tracks (scanStart s).core base resolver hits (reserve+1) :=')])

    def test_nonvacuous_inside_and_four_outside_branches(self):
        fixture = (ROOT/'tests/reference/e1m1-path-map-bounds.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('⟨5,[0,0,474]⟩', '⟨5,[0,474]⟩'),
                         ('if r=4 then 0x600003', 'if r=4 then 1'),
                         ('core.regs 2=(5#32)', 'core.regs 2=(7#32)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

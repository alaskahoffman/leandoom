"""Caller-to-scan join: actual CALL arguments, protected memory and return path."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map_caller as proof
HEADER = '''import Doom.Proofs.E1M1PathMapCaller
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapCaller
'''
ARGS = 's f base lines words c x y w h enabled dims mapX mapY globals inside valid image safe selected'


class PathMapCallerTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.bounds.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMapCaller.lean').read_text()
        declaration = source[source.index('theorem '+name):].split(' :=', 1)[0]
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
                    output+'extra', output.replace('first_scan_execution', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1PathMapCaller.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_all_extracted_segments_and_execution_entry(self):
        for key in ['dispatch', 'lineEntry', 'lineReturn', 'cell']:
            raw = copy.deepcopy(self.raw)
            raw[key] = bytes([raw[key][0] ^ 1])+raw[key][1:]
            with self.subTest(segment=key):
                self.rejects(proof.certificate(self.data, raw))
        self.mutations(self.contract('inside_to_scan', ARGS), [
            ('⟨s,f,0x2ca7f⟩', '⟨s,f,0x2ca86⟩'), ('∃ n≤30', '∃ n≤0'),
            ('s.regs 4-(12#32)', 's.regs 4-(8#32)')])

    def test_caller_must_supply_enabled_flag_coordinates_and_dimensions(self):
        self.mutations(self.contract('inside_to_scan', ARGS), [
            ('(enabled : OriginalPathCell.enabled true s=true)', '(enabled : True)'),
            ('(dims : Dimensions s w h)', '(dims : True)'),
            ('(mapX : s.regs 6=x.toBitVec)', '(mapX : s.regs 0=x.toBitVec)'),
            ('(mapY : s.regs 1=y.toBitVec)', '(mapY : s.regs 2=y.toBitVec)'),
            ('(globals : Globals s base lines)', '(globals : True)'),
            ('(selected : words[4+Collision.pathCellIndex x y w]?=some c.offset)', '(selected : True)')])

    def test_call_store_and_map_protection_cannot_be_dropped(self):
        self.mutations(self.contract('call_frame', 's a safe'), [
            ('(safe : Apart a (s.regs 4-(4#32)))', '(safe : True)')])
        self.mutations(self.contract('image_at_call', 's base words image safe'), [
            ('(safe : ImageSafe s base words)', '(safe : True)'),
            ('(image : WordImage s.memory base words)', '(image : True)')])
        self.mutations(self.contract('safe_at_call', 's a safe'), [('(safe : Safe s a)', '(safe : True)')])

    def test_outside_returns_through_the_real_success_test(self):
        self.mutations(self.contract('outside_to_things', 's f x y w h enabled dims mapX mapY outside'), [
            ('(outside : Collision.pathCellInside x y w h=false)', '(outside : True)'),
            ('(dims : Dimensions s w h)', '(dims : True)'),
            ('(enabled : OriginalPathCell.enabled true s=true)', '(enabled : True)'),
            ('(resumed s).pc=0x2ca9c', '(resumed s).pc=0x2cb0b'),
            ('(resumed s).core.regs 4=s.regs 4', '(resumed s).core.regs 4=s.regs 4-(4#32)'),
            ('(resumed s).core.regs 0=1', '(resumed s).core.regs 0=0')])

    def test_collection_is_preserved_without_free_capacity(self):
        self.mutations(self.contract('collection_preserved', 's base resolver hits reserve tracked cursorSafe recordsSafe'), [
            ('(cursorSafe : Safe s (0x2c028#32))', '(cursorSafe : True)'),
            ('(recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8], Safe s (base+BitVec.ofNat 32 (12*i)+off))', '(recordsSafe : True)'),
            ('OriginalLineCollection.Tracks (scan s).core base resolver hits reserve :=',
             'OriginalLineCollection.Tracks (scan s).core base resolver hits (reserve+1) :=')])

    def test_firing_join_derives_coordinates_but_keeps_map_obligations(self):
        args = ('gun s f weapon input ox oy sx sy ex ey geometry layout xout yout okX okY '
                'base lines words c w h dims globals inside valid image safe selected')
        self.mutations(self.contract('first_scan_execution', args), [
            ('(layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)', '(layout : True)'),
            ('(dims : Dimensions (E1M1PathGridSetup.firstGrid gun s).core w h)', '(dims : True)'),
            ('(image : WordImage (E1M1PathGridSetup.firstGrid gun s).core.memory base words)',
             '(image : WordImage s.memory base words)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun+1')])

    def test_nonvacuous_inside_and_four_outside_directions(self):
        fixture = (ROOT/'tests/reference/e1m1-path-map-caller.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('⟨5,[0,0,474]⟩', '⟨5,[0,474]⟩'),
                         ('if r=4 then 0x600007', 'if r=4 then 1'),
                         ('(0x600047,1)', '(0x600047,0)'),
                         ('core.regs 2=(5#32)', 'core.regs 2=(7#32)'),
                         ('0x600003=(0x2ca94#32)', '0x600003=(0x2cab1#32)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

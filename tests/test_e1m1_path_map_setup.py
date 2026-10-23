"""Transport map assumptions through initialization and both grid axes."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map_setup as proof
HEADER = '''import Doom.Proofs.E1M1PathMapSetup
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapSetup
attribute [local irreducible] E1M1PathMap.WordImage
'''


class PathMapSetupTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.caller.bounds.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMapSetup.lean').read_text()
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
                    output+'extra', output.replace('initial_collection_at_scan', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1PathMapSetup.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_each_setup_byte_range_is_bound_to_the_original(self):
        for key in proof.SEGMENTS:
            raw = copy.deepcopy(self.raw)
            raw[key] = bytes([raw[key][0] ^ 1])+raw[key][1:]
            with self.subTest(segment=key):
                self.rejects(proof.certificate(self.data, raw))

    def test_setup_word_preservation_requires_write_separation(self):
        self.mutations(self.contract('after_frame', 's a safe'), [
            ('(safe : StackSafe (s.regs 4) a)', '(safe : True)')])
        self.mutations(self.contract('grid_frame', 's ox oy sx sy ex ey geometry a safe'), [
            ('(safe : Safe s a)', '(safe : StackSafe (s.regs 4-(60#32)) a)'),
            ('(geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)', '(geometry : True)')])
        self.mutations(self.contract('grid_stack', 's ox oy sx sy ex ey geometry'), [
            ('s.regs 4-(60#32)', 's.regs 4-(56#32)')])

    def test_map_is_derived_from_traversal_entry(self):
        self.mutations(self.contract('map_at_grid', 's ox oy sx sy ex ey geometry base lines words w h map'), [
            ('(map : MapInputs s base lines words w h)', '(map : True)'),
            ('(geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)', '(geometry : True)'),
            ('WordImage (grid s).core.memory base words', 'WordImage (grid s).core.memory (base+2) words')])
        self.mutations(self.contract('caller_safe', 's ox oy sx sy ex ey geometry a safe'), [
            ('(safe : Safe s a)', '(safe : True)')])

    def test_collection_comes_from_init_and_needs_cursor_protection(self):
        self.mutations(self.contract('initial_collection_at_scan',
                                    's ox oy sx sy ex ey geometry words c valid resolver cursorSafe'), [
            ('(geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)', '(geometry : True)'),
            ('(valid : c.Valid words)', '(valid : True)'),
            ('(cursorSafe : StackSafe (s.regs 4-(60#32)) (0x2c028#32))', '(cursorSafe : True)'),
            ('resolver #[] c.ids.length :=', 'resolver #[] (c.ids.length+129) :='),
            (').core 0x2ba20 resolver #[]', ').core 0x2ba24 resolver #[]')])

    def test_shared_firing_join_retains_earlier_boundary_obligations(self):
        args = ('gun s f weapon input ox oy sx sy ex ey geometry layout xout yout okX okY '
                'base lines words c w h map cursorSafe inside valid selected')
        self.mutations(self.contract('first_scan_execution', args), [
            ('(map : MapInputs (E1M1AimSetup.firstTraversal gun s).core base lines words w h)',
             '(map : MapInputs s base lines words w h)'),
            ('(cursorSafe : StackSafe ((E1M1AimSetup.firstTraversal gun s).core.regs 4-(60#32)) (0x2c028#32))',
             '(cursorSafe : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun+1'),
            ('0x2ba20 (resolve lines) #[] c.ids.length', '0x2ba20 (resolve lines) #[] (c.ids.length+129)')])

    def test_concrete_all_axis_directions_and_cursor_reset(self):
        fixture = (ROOT/'tests/reference/e1m1-path-map-setup.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('⟨5,[0,0,474]⟩', '⟨5,[0,474]⟩'),
                         ('def base : Word := 0xfffffffb', 'def base : Word := 0x2ba10'),
                         ('(0x2c100,base+8)', '(0x2c100,base+10)'),
                         ('0x2c028=(0x2ba20#32)', '0x2c028=(0xdead00#32)'),
                         ('def direction (i : Nat) : Word := if i=0 then -1',
                          'def direction (i : Nat) : Word := if i=0 then 1')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

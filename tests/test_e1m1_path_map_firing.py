"""Protect map state through actual firing and bullet-slope calls."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map_firing as proof
HEADER = '''import Doom.Proofs.E1M1PathMapFiring
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapFiring
attribute [local irreducible] E1M1PathMap.WordImage
'''


class PathMapFiringTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.setup.setup.caller.bounds.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMapFiring.lean').read_text()
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
                    output+'extra', output.replace('query_frame', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1PathMapFiring.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_query_and_setup_bytes_are_pinned(self):
        for key in proof.SEGMENTS:
            raw = copy.deepcopy(self.raw)
            raw[key] = bytes([raw[key][0] ^ 1])+raw[key][1:]
            with self.subTest(segment=key):
                self.rejects(proof.certificate(self.data, raw))

    def test_stack_offsets(self):
        for name, args, old, new in [
                ('slope_stack', 's f', 's.regs 4-(20#32)', 's.regs 4-(16#32)'),
                ('aim_stack', 'gun s', 's.regs 4-(4#32)', 's.regs 4-(8#32)'),
                ('query_stack', 'gun s', 's.regs 4-(24#32)', 's.regs 4-(20#32)')]:
            self.mutations(self.contract(name, args), [(old, new)])

    def test_protected_memory_and_later_layout(self):
        for name in ['query_frame', 'query_safe']:
            self.mutations(self.contract(name, 'gun s a safe'), [
                ('(safe : Safe gun s a)', '(safe : True)')])
        source = HEADER+"""
example (gun : Fire.Gun) (s : X86Memory.State) (a : Word)
    (early : ∀ b∈E1M1DischargeSetters.beforeFlashWrites gun s, Apart a b)
    (flash : ∀ b∈E1M1FlashInstall.writes (E1M1DischargeSetters.flashCall gun s).core, Apart a b)
    (aim : Apart a (s.regs 4-(4#32)))
    (slope : ∀ b∈slopeWrites (E1M1DischargeSetters.aimCall gun s).core, Apart a b)
    (later : E1M1PathMapQuery.Safe (E1M1PathMapQuery.withStack s (s.regs 4-(24#32))) a) :
    Safe gun s a := ⟨early,flash,aim,slope,later⟩
"""
        self.mutations(source, [
            ('(early : ∀ b∈E1M1DischargeSetters.beforeFlashWrites gun s, Apart a b)', '(early : True)'),
            ('(flash : ∀ b∈E1M1FlashInstall.writes (E1M1DischargeSetters.flashCall gun s).core, Apart a b)', '(flash : True)'),
            ('(aim : Apart a (s.regs 4-(4#32)))', '(aim : True)'),
            ('(slope : ∀ b∈slopeWrites (E1M1DischargeSetters.aimCall gun s).core, Apart a b)', '(slope : True)'),
            ('(later : E1M1PathMapQuery.Safe (E1M1PathMapQuery.withStack s (s.regs 4-(24#32))) a)', '(later : True)')])

    def test_map_and_execution_require_post_sound_inputs(self):
        self.mutations(self.contract('map_at_query', 'gun s base lines words w h map'), [
            ('(map : MapInputs gun s base lines words w h)', '(map : True)'),
            ('E1M1PathMapQuery.MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words w h',
             'E1M1PathMapQuery.MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words (w+1) h')])
        self.mutations(self.contract('query_execution', 'gun s f weapon input base lines words w h map'), [
            ('(input : E1M1DischargeSetters.Inputs gun s weapon)', '(input : True)'),
            ('(map : MapInputs gun s base lines words w h)', '(map : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun-1')])

    def test_scan_join_and_cursor(self):
        args = ('gun s f weapon input ox oy sx sy ex ey geometry layout xout yout okX okY '
                'base lines words c w h map cursorSafe inside valid selected')
        self.mutations(self.contract('first_scan_execution', args), [
            ('(map : MapInputs gun s base lines words w h)', '(map : True)'),
            ('(geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)',
             '(geometry : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun-1'),
            ('0x2ba20 (resolve lines) #[] c.ids.length', '0x2ba20 (resolve lines) #[] (c.ids.length+129)')])
        self.mutations(self.contract('cursor_at_query', 'gun s safe'), [
            ('s.regs 4-(112#32)', 's.regs 4-(88#32)')])

    def test_both_weapons_with_actual_setters_and_wrapping_stack(self):
        fixture = (ROOT/'tests/reference/e1m1-path-map-firing.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('def base : Word := 0x900003', 'def base : Word := 0x6000df'),
                         ('(0x2c100,base+8)', '(0x2c100,base+10)'),
                         ('0xffffffe9=(0x2d7d5#32)', '0xffffffe9=(0x2bb80#32)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

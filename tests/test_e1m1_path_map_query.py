"""Protect map state through the aim query and ray setup."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_path_map_query as proof
HEADER = '''import Doom.Proofs.E1M1PathMapQuery
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1PathMapQuery
attribute [local irreducible] E1M1PathMap.WordImage
'''


class PathMapQueryTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.setup.caller.bounds.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1PathMapQuery.lean').read_text()
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
                    output+'extra', output.replace('origins_at_traversal', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1PathMapQuery.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_query_and_setup_bytes_are_pinned(self):
        for key in proof.SEGMENTS:
            raw = copy.deepcopy(self.raw)
            raw[key] = bytes([raw[key][0] ^ 1])+raw[key][1:]
            with self.subTest(segment=key):
                self.rejects(proof.certificate(self.data, raw))

    def test_stack_offsets_and_protected_write_footprints(self):
        self.mutations(self.contract('ray_stack', 's'), [('s.regs 4-(16#32)', 's.regs 4-(12#32)')])
        self.mutations(self.contract('traversal_stack', 's'), [('s.regs 4-(28#32)', 's.regs 4-(24#32)')])
        for theorem in ['setup_safe', 'traversal_safe', 'traversal_frame']:
            self.mutations(self.contract(theorem, 's a safe'), [('(safe : Safe s a)', '(safe : True)')])

    def test_query_execution_and_earlier_map_contract(self):
        self.mutations(self.contract('query_execution', 's f base lines words w h map'), [
            ('(map : MapInputs s base lines words w h)', '(map : True)'),
            ('[] 36 ⟨s,f,0x2bb80⟩', '[] 35 ⟨s,f,0x2bb80⟩'),
            ('[] 36 ⟨s,f,0x2bb80⟩', '[] 36 ⟨s,f,0x2bba0⟩')])
        self.mutations(self.contract('map_at_traversal', 's base lines words w h map'), [
            ('(map : MapInputs s base lines words w h)', '(map : True)'),
            ('E1M1PathMapSetup.MapInputs (traversal s).core base lines words w h',
             'E1M1PathMapSetup.MapInputs (traversal s).core base lines words (w+1) h')])

    def test_origins_require_initial_values_and_protection(self):
        self.mutations(self.contract('origins_at_traversal', 's ox oy x y safeX safeY'), [
            ('(x : load32 s.memory 0x2c104=ox.raw.toBitVec)', '(x : True)'),
            ('(y : load32 s.memory 0x2c108=oy.raw.toBitVec)', '(y : True)'),
            ('(safeX : Safe s (0x2c104#32))', '(safeX : True)'),
            ('(safeY : Safe s (0x2c108#32))', '(safeY : True)')])
        self.mutations(self.contract('cursor_at_traversal', 's safe'), [
            ('(safe : E1M1PathMapSetup.StackSafe (s.regs 4-(88#32)) (0x2c028#32))', '(safe : True)'),
            ('s.regs 4-(88#32)', 's.regs 4-(60#32)')])

    def test_shared_scan_join_keeps_pre_query_firing_obligation(self):
        args = ('gun s f weapon input ox oy sx sy ex ey geometry layout xout yout okX okY '
                'base lines words c w h map cursorSafe inside valid selected')
        self.mutations(self.contract('first_scan_execution', args), [
            ('(map : MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words w h)',
             '(map : MapInputs s base lines words w h)'),
            ('(cursorSafe : E1M1PathMapSetup.StackSafe ((E1M1BulletAim.firstQuery gun s).core.regs 4-(88#32)) (0x2c028#32))',
             '(cursorSafe : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun+1'),
            ('0x2ba20 (resolve lines) #[] c.ids.length', '0x2ba20 (resolve lines) #[] (c.ids.length+129)')])

    def test_concrete_writes_and_protected_map(self):
        fixture = (ROOT/'tests/reference/e1m1-path-map-query.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('def base : Word := 0xfffffffb', 'def base : Word := 0x2b9ac'),
                         ('(0x2c100,base+8)', '(0x2c100,base+10)'),
                         ('0x600043=(0x2bbff#32)', '0x600043=(0x2bb80#32)'),
                         ('0x2b9f8=0 :=', '0x2b9f8=0x12345678 :='),
                         ('0x2c104=(0xffff0000#32)', '0x2c104=(0#32)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

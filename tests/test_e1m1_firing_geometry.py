"""Connect post-sound shooter/table data to query geometry."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_firing_geometry as proof
HEADER = '''import Doom.Proofs.E1M1FiringGeometry
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1FiringGeometry
open E1M1PathMapQuery (traversal withStack)
open E1M1PathMapFiring (Safe)
attribute [local irreducible] E1M1PathMap.WordImage Collision.SolidThing.attackEndpoint
'''


class FiringGeometryTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1FiringGeometry.lean').read_text()
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
                    output+'extra', output.replace('query_geometry', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1FiringGeometry.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_actor_pointer_and_aim_frame(self):
        self.mutations(self.contract('aim_actor', 'gun s actor value safe'), [
            ('(value : load32 s.memory (s.regs 1)=actor)', '(value : True)'),
            ('(safe : Safe gun s (s.regs 1))', '(safe : True)'),
            ('(E1M1DischargeSetters.aimCall gun s).core.regs 0=actor',
             '(E1M1DischargeSetters.aimCall gun s).core.regs 0=actor+1')])
        self.mutations(self.contract('aim_frame', 'gun s a h'), [
            ('(h : Safe gun s a)', '(h : True)')])

    def test_first_query_arguments(self):
        self.mutations(self.contract('first_request', 'gun s actor angle pointer pointerSafe value angleSafe'), [
            ('(pointerSafe : Safe gun s (s.regs 1))', '(pointerSafe : True)'),
            ('(value : load32 s.memory (actor+32)=angle.raw.toBitVec)', '(value : True)'),
            ('(angleSafe : Safe gun s (actor+32))', '(angleSafe : True)'),
            ('(Fixed.ofInt 1024).raw.toBitVec', '(Fixed.ofInt 2048).raw.toBitVec')])

    def test_stack_layout_transport(self):
        for name in ['aim_layout', 'flag_layout', 'path_layout']:
            self.mutations(self.contract(name, 's q sp h'), [
                ('(sp : q.regs 4=s.regs 4-(24#32))', '(sp : q.regs 4=s.regs 4-(20#32))')])

    def test_query_geometry_transport(self):
        self.mutations(self.contract('query_geometry', 'gun s actor thing angle ox oy h'), [
            ('(h : Inputs gun s actor thing angle ox oy)', '(h : True)'),
            ('E1M1AimGeometry.Inputs (E1M1BulletAim.firstQuery gun s).core thing angle (Fixed.ofInt 1024) ox oy',
             'E1M1AimGeometry.Inputs (E1M1BulletAim.firstQuery gun s).core thing angle (Fixed.ofInt 1024) oy ox')])

    def test_path_and_scan_joins(self):
        self.mutations(self.contract('first_path_correspondence', 'gun s f weapon input actor thing angle ox oy geometry'), [
            ('(input : E1M1DischargeSetters.Inputs gun s weapon)', '(input : True)'),
            ('(geometry : Inputs gun s actor thing angle ox oy)', '(geometry : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun-1')])
        args = ('gun s f weapon input actor thing angle ox oy geometry xout yout okX okY '
                'base lines words c w h map cursorSafe inside valid selected')
        self.mutations(self.contract('first_scan_execution', args), [
            ('(geometry : Inputs gun s actor thing angle ox oy)', '(geometry : True)'),
            ('(map : E1M1PathMapFiring.MapInputs gun s base lines words w h)', '(map : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun-1')])

    def test_both_weapons_concrete_geometry(self):
        fixture = (ROOT/'tests/reference/e1m1-firing-geometry.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('(0x600421,angle.raw.toBitVec)', '(0x600421,0x40000000)'),
                         ('(0x13584,0x7a84)', '(0x13584,0x7a88)'),
                         ('(0x2c104,0xffff0000)', '(0x2c104,0x10000)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

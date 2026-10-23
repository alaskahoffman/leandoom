"""Connect query-entry shooter/table data to traversal geometry."""
import copy
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_aim_geometry as proof
HEADER = '''import Doom.Proofs.E1M1AimGeometry
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1PathMap E1M1PathMapLookup E1M1AimGeometry
open E1M1PathMapQuery (traversal)
attribute [local irreducible] E1M1PathMap.WordImage Collision.SolidThing.attackEndpoint
'''


class AimGeometryTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    @classmethod
    def setUpClass(cls):
        cls.data, _ = proof.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
        cls.spec, cls.profile, cls.raw = proof.extracted()
        cls.source = proof.certificate(cls.data, cls.raw)

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1AimGeometry.lean').read_text()
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
                    output+'extra', output.replace('path_inputs', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1AimGeometry.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_selected_samples_are_required(self):
        self.mutations(self.contract('selected_samples', 's angle distance h'), [
            ('(h : RaySamples s angle distance)', '(h : True)')])
        self.mutations(self.contract('endpoint', 's thing angle distance h'), [
            ('(h : RaySamples s angle distance)', '(h : True)'),
            ('(thing.attackEndpoint angle distance).1.raw.toBitVec,',
             '(thing.attackEndpoint angle distance).2.raw.toBitVec,')])

    def test_setup_and_path_inputs_are_derived(self):
        for theorem in ['setup_inputs', 'path_inputs']:
            self.mutations(self.contract(theorem, 's thing angle distance ox oy h'), [
                ('(h : Inputs s thing angle distance ox oy)', '(h : True)')])
        self.mutations(self.contract('path_inputs', 's thing angle distance ox oy h'), [
            ('ox oy thing.x thing.y', 'ox oy thing.y thing.x'),
            ('(thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2',
             '(thing.attackEndpoint angle distance).2 (thing.attackEndpoint angle distance).1')])

    def test_continuous_query_execution(self):
        self.mutations(self.contract('query_path_correspondence', 's f thing angle distance ox oy h'), [
            ('⟨s,f,0x2bb80⟩', '⟨s,f,0x2bba0⟩'),
            ('(h : Inputs s thing angle distance ox oy)', '(h : True)')])

    def test_firing_join_retains_earlier_geometry_and_map_obligations(self):
        args = ('gun s f weapon input thing angle ox oy geometry xout yout okX okY '
                'base lines words c w h map cursorSafe inside valid selected')
        self.mutations(self.contract('first_scan_execution', args), [
            ('(geometry : Inputs (E1M1BulletAim.firstQuery gun s).core thing angle (Fixed.ofInt 1024) ox oy)',
             '(geometry : Inputs s thing angle (Fixed.ofInt 1024) ox oy)'),
            ('(map : E1M1PathMapFiring.MapInputs gun s base lines words w h)', '(map : True)'),
            ('OriginalWeaponDischarge.afterSound gun', 'OriginalWeaponDischarge.afterSound gun-1')])

    def test_geometry_fixture_and_mutations(self):
        fixture = (ROOT/'tests/reference/e1m1-aim-geometry.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        for old, new in [('(0x13584,0x7a84)', '(0x13584,0x7a88)'),
                         ('(0x2c104#32,0xffff0000#32)', '(0x2c104#32,0x10000#32)'),
                         ('(28*65536#32)', '(36*65536#32)')]:
            self.assertIn(old, fixture)
            self.rejects(fixture.replace(old, new))


if __name__ == '__main__':
    unittest.main()

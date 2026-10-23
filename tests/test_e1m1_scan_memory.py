"""First-scan memory and visit epoch contracts, with strict kernel audits."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_scan_memory as proof
HEADER = '''import Doom.Proofs.E1M1ScanMemory
set_option backward.isDefEq.respectTransparency true
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory
attribute [local irreducible] Collision.SolidThing.attackEndpoint E1M1PathMap.resolve
'''


class ScanMemoryTests(unittest.TestCase):
    lean = runtime.WeaponRuntimeTests.lean
    succeeds = runtime.WeaponRuntimeTests.succeeds

    def rejects(self, source):
        result = self.lean(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('error:', result.stdout)
        for bad in ['maximum', 'timeout', 'object file', 'unknown module prefix']:
            self.assertNotIn(bad, result.stdout.lower())

    def contract(self, name, args):
        source = (ROOT/'Doom/Proofs/E1M1ScanMemory.lean').read_text()
        declaration = re.split(r' :=(?: by)?\n', source[source.index('theorem '+name):], maxsplit=1)[0]
        return HEADER+declaration.replace('theorem '+name, 'example', 1)+' :=\n  '+name+' '+args+'\n'

    def mutations(self, source, changes):
        self.succeeds(source)
        for old, new in changes:
            self.assertIn(old, source)
            with self.subTest(change=old):
                self.rejects(source.replace(old, new))

    def test_certificate_and_strict_audit(self):
        data, _ = proof.previous.previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
        _, _, raw = proof.extracted()
        output = self.succeeds(proof.certificate(data, raw))
        proof.audit(output)
        for bad in [output.replace('Quot.sound', 'sorryAx'), output.replace('Quot.sound', 'native.ax'),
                    output+'extra', output.replace('firing_seen', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)
        text = (ROOT/'Doom/Proofs/E1M1ScanMemory.lean').read_text()
        self.assertEqual(proof.PROOFS, re.findall(r'^theorem (\w+)', text, re.M))

    def test_memory_protection(self):
        self.mutations(self.contract('caller_frame', 's a safe'), [
            ('(safe : E1M1PathMapCaller.Safe s a)', '(safe : True)')])
        self.mutations(self.contract('firing_frame', 'gun s actor thing angle ox oy geometry a safe'), [
            ('(safe : E1M1PathMapFiring.Safe gun s a)', '(safe : True)'),
            ('(geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)', '(geometry : True)')])
        self.mutations(self.contract('before_init_frame', 'gun s a safe'), [
            ('(safe : BeforeInit gun s a)', '(safe : True)')])

    def test_loaded_line_geometry(self):
        self.mutations(self.contract('firing_line', 'gun s actor thing angle ox oy geometry line p v w encoded safe'), [
            ('(encoded : LineWords s.memory line p v w)', '(encoded : True)'),
            ('(safe : ∀ a∈lineReads p v w, E1M1PathMapFiring.Safe gun s a)', '(safe : True)'),
            ('LineWords (firstScan gun s).core.memory line p v w',
             'LineWords (firstScan gun s).core.memory line p w v')])

    def test_initialized_trace(self):
        self.mutations(self.contract('firing_initialized_frame', 'gun s actor thing angle ox oy geometry a safe'), [
            ('(safe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) a)', '(safe : True)')])
        self.mutations(self.contract('firing_trace', 'gun s actor thing angle ox oy geometry safe'), [
            ('(s.regs 4-(112#32))', '(s.regs 4-(108#32))'),
            ('(trace.x.raw.toBitVec,trace.y.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec)',
             '(trace.y.raw.toBitVec,trace.x.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec)')])

    def test_epoch_and_initial_seen_relation(self):
        self.mutations(self.contract('firing_epoch', 'gun s actor thing angle ox oy geometry before after'), [
            ('(before : BeforeInit gun s (0x13580#32))', '(before : True)'),
            ('(after : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))', '(after : True)'),
            ('load32 s.memory 0x13580+(1#32)', 'load32 s.memory 0x13580+(2#32)')])
        self.mutations(self.contract('firing_seen', 'gun s actor thing angle ox oy geometry before after lines c items i safe'), [
            ('(items : E1M1PathMapLookup.ScanWords (firstScan gun s).core lines c)', '(items : True)'),
            ('(safe : E1M1PathMapFiring.Safe gun s (E1M1PathMap.resolve lines ⟨(Fixed.ofInt 0),true,c.ids[i.val]⟩+54))', '(safe : True)'),
            ('load32 s.memory 0x13580+(1#32)', 'load32 s.memory 0x13580+(2#32)')])

    def test_wrapping_epoch_and_trace_fixture(self):
        fixture = (ROOT/'tests/reference/e1m1-scan-memory.lean').read_text()
        output = self.succeeds(fixture)
        self.assertNotIn('sorryAx', output)
        self.assertNotIn('_native', output)
        self.rejects(fixture.replace('(0x13580,0xffffffff)', '(0x13580,0xfffffffe)'))
        self.rejects(fixture.replace('(lines+8,4*65536)', '(lines+8,5*65536)'))


if __name__ == '__main__':
    unittest.main()

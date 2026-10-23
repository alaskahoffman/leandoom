"""Fixed E1M1 target, kernel certificate, and contract rejection tests."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_e1m1_death as proof


class E1M1DeathTests(unittest.TestCase):
    def setUp(self):
        self.profile = json.loads(proof.PROFILE.read_text())
        self.executable = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        self.shareware = json.loads((ROOT/'tests/reference/shareware.json').read_text())

    def lean(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'Check.lean'
            path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def reject_contracts(self, replacements):
        source = proof.certificate()
        for old, new in replacements:
            with self.subTest(change=new):
                self.assertIn(old, source)
                result = self.lean(source.replace(old, new))
                self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
                self.assertIn('error:', result.stdout)

    def test_fixed_profile_matches_comparison(self):
        proof.check_profile(self.profile, self.executable, self.shareware)
        with patch.object(proof.demo_compare, 'HEADER', bytes([0])*13):
            with self.assertRaisesRegex(ValueError, 'comparison header'):
                proof.check_profile(self.profile, self.executable, self.shareware)

    def test_different_setup_rejected(self):
        for field, value in [('episode', 2), ('map', 2), ('skill', 0), ('console_player', 1),
                             ('players', [True, True, False, False]), ('netgame', True),
                             ('deathmatch', True), ('respawn', True), ('fast', True),
                             ('nomonsters', True), ('automap', True),
                             ('exe_sha256', 'wrong'), ('wad_sha256', 'wrong'),
                             ('demo_header_hex', '00'*13), ('skill', True)]:
            with self.subTest(field=field):
                changed = copy.deepcopy(self.profile)
                changed[field] = value
                with self.assertRaisesRegex(ValueError, 'profile mismatch'):
                    proof.check_profile(changed, self.executable, self.shareware)

    def test_certificate_and_strict_axiom_audit(self):
        result = self.lean(proof.certificate())
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        proof.audit(result.stdout)
        for bad in [result.stdout.replace('Quot.sound', 'sorryAx'),
                    result.stdout.replace('Quot.sound', 'bad._native.ax_1'),
                    result.stdout+'unexpected', result.stdout.replace('floor_checked', 'missing')]:
            with self.assertRaises(ValueError):
                proof.audit(bad)

    def test_entry_and_memory_contracts_required(self):
        self.reject_contracts([
            ('(site : pc ∈ PlayerDamageEntry.sites)', '(site : True)'),
            ('(h : KillDeathBranches.Inputs s v d false 0 body sim.deathWorld w y)', '(h : True)'),
            ('(dead : (PlayerDamage.apply v d none false false sim.rng).killed=true)', '(dead : True)'),
            ('(stackSafe : Apart (0x12c5c#32) (s.regs 4-(56#32)))', '(stackSafe : True)'),
            ('(info : body.info=E1M1Death.playerInfo)', '(info : True)')])

    def test_fixed_profile_contracts_required(self):
        self.reject_contracts([
            ('(map : sim.map.name="E1M1")', '(map : sim.map.name="E1M2")'),
            ('(skill : load32 s.memory (0x2b3e0#32)=2)', '(skill : load32 s.memory (0x2b3e0#32)=0)'),
            ('Inputs s v d false 0 body', 'Inputs s v d true 0 body')])

    def test_wrong_handoff_results_rejected(self):
        self.reject_contracts([
            ('[0x30ea0] 239', '[0x30ea0] 1'),
            ('(t.core.regs 2=158 ∨ t.core.regs 2=165)', '(t.core.regs 2=158 ∨ t.core.regs 2=166)'),
            ('load32 t.core.memory (0x12c5c#32)=0', 'load32 t.core.memory (0x12c5c#32)=1'),
            ('(s.regs 4-56)=0x2a3f1', '(s.regs 4-56)=0x2a3c8'),
            ('(PlayerDamage.apply v d none false false sim.rng).state.health E1M1Death.playerInfo',
             'v.health E1M1Death.playerInfo')])


if __name__ == '__main__':
    unittest.main()

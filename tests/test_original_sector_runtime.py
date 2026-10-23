"""Live phase binding, synchronized inputs, failure state, and proof boundaries."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import verify_original_sector_joined as proof


class SectorRuntimeTests(unittest.TestCase):
    def setUp(self):
        spec = json.loads((ROOT/'tests/reference/original-sector-joined.json').read_text())
        self.raw = {k: bytes.fromhex(v['hex']) for k, v in spec['units'].items()}

    def lean(self, source):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'Runtime.lean'
            path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                  cwd=ROOT, capture_output=True, text=True)

    def certificate_parts(self):
        return proof.certificate(self.raw, 'test').split('theorem live_runtime_checked', 1)

    def test_live_certificate_and_strict_axiom_audit(self):
        r = self.lean(proof.certificate(self.raw, 'test'))
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)
        proof.audit(r.stdout)
        self.assertIn("'Doom.Proofs.SectorRuntime.correspondence' depends on axioms:", r.stdout)
        self.assertIn("'Doom.Proofs.SectorRuntime.phase_continuation'", r.stdout)
        with self.assertRaises(ValueError):
            proof.audit(r.stdout.replace('Quot.sound', 'sorryAx'))

    def test_initial_runtime_contracts_cannot_be_dropped(self):
        head, body = self.certificate_parts()
        premises = [
            ('sync', '(sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)'),
            ('found', '(found : scene.things[0]? = some actor)'),
            ('supported', '(supported : actor.moveFlags.floating = false)'),
            ('lookup', '(lookup : s.map.sectorAt actor.x actor.y = .ok index)'),
            ('valid', '(valid : index < s.map.sectors.size)'),
            ('secretSector', '(secretSector : s.map.sectors[index]!.special = 9)'),
        ]
        for name, premise in premises:
            with self.subTest(premise=name):
                bad = body.replace(premise, '')
                before, application = bad.split('  exact SectorRuntime.correspondence', 1)
                import re
                application = re.sub(r'\b'+name+r'\b', '(by assumption)', application, count=1)
                r = self.lean(head+'theorem live_runtime_checked'+before+'  exact SectorRuntime.correspondence'+application)
                self.assertNotEqual(r.returncode, 0)
                self.assertIn('assumption', r.stdout)
                with self.assertRaises(ValueError): proof.audit(r.stdout)

    def test_wrong_actor_floor_or_command_relation_rejected(self):
        head, body = self.certificate_parts()
        for old, new in [
            ('(actor.motion s.player.body)', 's.player.body'),
            ('(Doom.Fixed.ofInt s.map.sectors[index]!.floor) s.secrets', 'actor.floor s.secrets'),
            ('(s.prepareSectorTick keys (some cmd))', '(s.prepareSectorTick keys none)'),
            ('SectorRuntime.output index', 'SectorRuntime.output (index+1)'),
        ]:
            with self.subTest(replacement=new):
                self.assertIn(old, body)
                r = self.lean(head+'theorem live_runtime_checked'+body.replace(old, new))
                self.assertNotEqual(r.returncode, 0)
                self.assertIn('mismatch', r.stdout.lower())
                with self.assertRaises(ValueError): proof.audit(r.stdout)

    def test_real_phase_position_counter_wrap_repeat_and_failure_state(self):
        r = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean',
                            str(ROOT/'tests/reference/sector-runtime.lean')],
                           cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)
        self.assertEqual(r.stdout.strip(), '[true, true, true, true, true, true]')

    def test_error_observation_and_unrelated_sector_frame(self):
        r = self.lean('''import Doom.Proofs.OriginalSectorRuntime
open Doom Doom.Proofs Doom.Proofs.SectorRuntime
example (failed : Simulation) (index : Nat) : output index (.error failed) = none := rfl
example (s : Simulation) (q : Player) (index other : Nat) (different : index ≠ other) :
    (result s q index).map.sectors[other]! = s.map.sectors[other]! :=
  Array.getElem!_set!_ne _ _ _ _ different
example (s : Simulation) (q : Player) (index : Nat) :
    (result s q index).rng = s.rng ∧ (result s q index).inventory = s.inventory := ⟨rfl,rfl⟩
''')
        self.assertEqual(r.returncode, 0, r.stdout+r.stderr)


if __name__ == '__main__':
    unittest.main()

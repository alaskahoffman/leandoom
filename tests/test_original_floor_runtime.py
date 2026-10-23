"""Bind original floor proofs to actual preparation/request/combat callbacks."""
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_original_floor_joined as proof

class FloorRuntimeTests(unittest.TestCase):
    def setUp(self):
        spec=json.loads((ROOT/'tests/reference/original-floor-joined.json').read_text())
        self.raw={k:bytes.fromhex(v['hex']) for k,v in spec['units'].items()}
        self.raw['randomTableBytes']=bytes.fromhex(json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())['units']['randomTableBytes']['hex'])

    def lean(self,source):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Runtime.lean';path.write_text(source)
            return subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)

    def test_live_certificate_includes_real_callback_and_no_extra_axioms(self):
        result=self.lean(proof.certificate(self.raw,'test'))
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        proof.audit(result.stdout)
        for name in ['FloorRuntime.correspondence','FloorRuntime.phase_handoff','Simulation.hurtFromFloor_request']:
            self.assertIn(name,result.stdout)
        for bad in [result.stdout.replace('Quot.sound','sorryAx'),
                    result.stdout.replace('Quot.sound','unchecked._native.ax_1'),
                    result.stdout.replace('FloorRuntime.phase_handoff','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)

    def test_initial_runtime_premises_are_required(self):
        head,body=proof.certificate(self.raw,'test').split('theorem live_runtime_checked',1)
        for name,premise in [
            ('sync','(sync : (SectorRuntime.inputPlayer s).syncScene s.map = .ok scene)'),
            ('found','(found : scene.things[0]? = some actor)'),
            ('supported','(supported : actor.moveFlags.floating = false)'),
            ('lookup','(lookup : s.map.sectorAt actor.x actor.y = .ok index)'),
            ('valid','(valid : index < s.map.sectors.size)'),
            ('special','(special : s.map.sectors[index]!.special = kind.special)'),
        ]:
            with self.subTest(premise=name):
                self.assertIn(premise,body)
                before,application=body.replace(premise,'').split('  exact FloorRuntime.correspondence',1)
                application=re.sub(r'\b'+name+r'\b','(by assumption)',application,count=1)
                result=self.lean(head+'theorem live_runtime_checked'+before+'  exact FloorRuntime.correspondence'+application)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('assumption',result.stdout)
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_wrong_position_floor_suit_clock_rng_and_command_bindings_rejected(self):
        head,body=proof.certificate(self.raw,'test').split('theorem live_runtime_checked',1)
        for old,new in [
            ('(actor.motion s.player.body)','s.player.body'),
            ('(Doom.Fixed.ofInt s.map.sectors[index]!.floor)','actor.floor'),
            ('(s.inventory.suit > 0)','(s.player.inventory.suit > 0)'),
            ('(s.ticks-1)','s.ticks'),
            ('s.rng) :','{ s.rng with play := s.rng.play+1 }) :'),
            ('(s.prepareSectorTick keys (some cmd))','(s.prepareSectorTick keys none)'),
        ]:
            with self.subTest(replacement=new):
                self.assertIn(old,body)
                result=self.lean(head+'theorem live_runtime_checked'+body.replace(old,new))
                self.assertNotEqual(result.returncode,0)
                self.assertIn('mismatch',result.stdout.lower())
                with self.assertRaises(ValueError):proof.audit(result.stdout)

    def test_real_phase_synchronized_position_rng_handoff_and_errors(self):
        result=self.lean((ROOT/'tests/reference/floor-runtime.lean').read_text())
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertEqual(result.stdout.strip(),'['+', '.join(['true']*13)+']')

    def test_original_inline_behavior_and_no_damage_combat_branch(self):
        result=self.lean('''import Doom.Proofs.OriginalFloorRuntime
open Doom Doom.Proofs
example (s : Simulation) (damage : Simulation → Nat → Simulation) :
    s.applyFloorEffect damage =
      match s.map.sectorAt s.player.body.x s.player.body.y with
      | .error error => { s with physicsError := some error }
      | .ok index =>
        let sector := s.map.sectors[index]!
        let (amount,rng) := LevelSpecials.floorDamage sector.special s.player.body.z
          (Fixed.ofInt sector.floor) (s.inventory.suit > 0) (s.ticks-1) s.rng
        let next := { s with rng }
        if amount == 0 then next else damage next amount := FloorRuntime.effect_inline s damage
example (s : Simulation) (rng : DoomRandom) (h : s.floorDamageRequest = .ok (0,rng)) :
    s.hurtFromFloor = { s with rng } := FloorRuntime.combat_no_damage s rng h
example (failed : Simulation) : FloorRuntime.output (.error failed) = none := rfl
''')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':unittest.main()

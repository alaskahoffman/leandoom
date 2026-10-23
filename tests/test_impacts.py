"""Effect state/RNG parity and live nonblocking sprites."""
import hashlib
import json
from pathlib import Path
import subprocess
import unittest
import impact_reference as reference
import test_assets
from test_assets import patch,replace
from test_combat import arena,combat_art
ROOT=reference.ROOT


class ImpactTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geometry,script):
        path=self.directory/'state.json'
        self.run_cli(['combat','E1M1',script,path],geometry)
        return json.loads(path.read_text())

    def test_generated_metadata(self):
        subprocess.run(['python3',str(ROOT/'scripts/generate-impact.py')],check=True,capture_output=True)

    def test_original_spawn_motion_and_removal_at_both_optimizations(self):
        commands=reference.corpus();path=self.directory/'commands.txt'
        path.write_text('\n'.join(commands)+'\n')
        output=self.directory/'lean.txt'
        subprocess.run([str(ROOT/'.lake/build/bin/impact-probe'),str(path),str(output)],check=True,capture_output=True)
        lean=output.read_bytes();source=self.directory/'reference.c';source.write_text(reference.source())
        for optimization in ['-O0','-O2']:
            binary=self.directory/('reference'+optimization)
            subprocess.run(['cc','-std=c11','-fwrapv',optimization,str(source),'-o',str(binary)],check=True,capture_output=True)
            c=subprocess.check_output([str(binary),str(path)])
            self.assertEqual(hashlib.sha256(lean).hexdigest(),hashlib.sha256(c).hexdigest(),optimization)
        self.assertEqual(len(lean.splitlines()),sum(int(c.split()[-1])+1 for c in commands))

    def test_wall_puff_spawns_ticks_and_expires_without_blocking_movement(self):
        first=self.state(arena(),'19:8192')
        self.assertEqual(first['shots'],1)
        self.assertEqual(len(first['impacts']),1)
        self.assertEqual(first['rng'],6) # Player spawn, damage, four effect draws.
        self.assertEqual(first['impacts'][0]['momz'],1)
        self.assertEqual(first['impacts'][0]['tics'],2) # 4-(149&3)-first thinker tic.
        self.assertEqual(self.state(arena(),'19:8192,30:0')['impacts'],[])
        self.assertEqual(self.state(arena(),'19:8192,1:1024'),self.state(arena(),'0:0'))
        a=self.state(arena(),'19:8192,10:2');b=self.state(arena(),'19:0,10:2')
        self.assertEqual((a['x'],a['y'],a['momentum']),(b['x'],b['y'],b['momentum']))

    def test_blood_spawns_before_pain_rng_and_replaces_small_damage_countdown(self):
        s=self.state(arena([(96,0,0,3004,7)]),'19:8192')
        self.assertEqual([e['kind'] for e in s['shotEvents']],['blood','damage'])
        self.assertEqual(s['actors'][0]['health'],15)
        self.assertEqual(s['rng'],10) # Three map draws, alert, damage, four spawn draws, pain.
        self.assertEqual(len(s['impacts']),1)
        p=s['impacts'][0]
        self.assertEqual(p['tics'],7) # Small blood resets to 8, then creation-tic tick.
        self.assertEqual(p['momz'],1) # Starts at 2; gravity runs after first movement.

    def test_shotgun_wall_impacts_interleave_four_draws_per_pellet(self):
        geometry=arena(extras=[(0,0,0,2001,7)])
        s=self.state(geometry,'1:2,45:0,4:8192')
        self.assertEqual(s['shots'],1)
        self.assertEqual(len(s['impacts']),7)
        self.assertEqual(s['rng'],51) # Two map draws + seven*(damage+spread+impact).

    def test_miss_without_an_impact_does_not_consume_effect_randomness(self):
        # At angle zero the fine cosine is 65535/65536, so the 2048-unit
        # wall lies just beyond the trace endpoint. Avoid oversized-map overflow.
        s=self.state(arena(size=2048),'19:8192')
        self.assertEqual(s['shots'],1)
        self.assertEqual(s['shotEvents'],[])
        self.assertEqual(s['impacts'],[])
        self.assertEqual(s['rng'],2) # Player spawn and damage only; no object hit.

    def test_puff_sprite_is_drawn_from_the_live_effect(self):
        geometry=arena(size=96)+combat_art()
        frames=[]
        for color in [200,201]:
            art=geometry
            for label in ['PUFFA0','PUFFB0','PUFFC0','PUFFD0']:
                art=replace(art,label,patch([[color]*12 for _ in range(12)],6,6))
            out=self.directory/f'impact-{color}.ppm'
            self.run_cli(['render-combat','E1M1','19:8192',out],art)
            frames.append(out.read_bytes())
        self.assertNotEqual(hashlib.sha256(frames[0]).digest(),hashlib.sha256(frames[1]).digest())


if __name__=='__main__':unittest.main()

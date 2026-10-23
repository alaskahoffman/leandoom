"""Death actions through real map links, collision, pickups and game ticks.

The diagnostic injects already-lethal signed health; it does not stand in for
the still-unported P_DamageMobj damage/thrust/pain routine.
"""
import json
from pathlib import Path
import subprocess
import unittest
import test_assets
from test_combat import arena
from test_wad import wad

ROOT = Path(__file__).resolve().parents[1]


class DeathTests(unittest.TestCase):
    setUp = test_assets.AssetTests.setUp
    tearDown = test_assets.AssetTests.tearDown

    def sim(self, health=0, script='0:0', kind=3004, target=1, enemies=None):
        path = self.directory/'death.wad'
        path.write_bytes(wad(arena(enemies if enemies is not None else [(48,0,0,kind,7)])))
        output = self.directory/'death.json'
        subprocess.run([str(ROOT/'.lake/build/bin/death-probe'), 'runtime', str(path),
                        str(target), str(health), script, str(output)],
                       check=True, capture_output=True, text=True, timeout=15)
        return json.loads(output.read_text())

    def test_generated_original_state_table(self):
        subprocess.run(['python3', str(ROOT/'scripts/generate-death.py')],
                       check=True, capture_output=True, timeout=15)

    def test_initial_flags_height_identity_and_immediate_drop(self):
        state = self.sim(-20)
        actor = state['actors'][0]
        death = actor['death']
        self.assertEqual((actor['thing'],actor['kind'],actor['health']), (1,3004,0))
        self.assertEqual((death['health'],death['height'],death['state'],death['tics']),
                         (-20,14,'S_POSS_DIE1',3))
        self.assertTrue(death['solid'])
        self.assertFalse(death['flags'] & 4)
        self.assertEqual(death['flags'] & (0x100000|0x400),0x100400)
        self.assertEqual((state['kills'],state['dropped'],state['rng']),(1,[2],5))

    def test_drop_preserves_fractional_xy_uses_floor_and_keeps_single_links(self):
        path = self.directory/'fractional.wad'
        path.write_bytes(wad(arena([(48,0,0,3004,7)])))
        output = self.directory/'fractional.json'
        for x,y in [(48*65536+32768,-1),(48*65536-1,32767)]:
            for script in ['0:0','1:0']:
                subprocess.run([str(ROOT/'.lake/build/bin/death-probe'),
                    'runtime-position',str(x),str(y),str(24*65536),str(path),
                    '1','0',script,str(output)],check=True,capture_output=True,timeout=15)
                drop=json.loads(output.read_text())['dropBodies'][0]
                # P_KillMobj: P_SpawnMobj(target->x,target->y,ONFLOORZ,...).
                self.assertEqual(drop['position'],[x,y,drop['floor']])
                self.assertTrue(drop['dropped'])
                self.assertEqual((drop['blockLinks'],drop['sectorLinks']),(1,1))

    def test_strict_extreme_death_threshold_and_sprite_selection(self):
        for kind, threshold, prefix in [(3004,-20,'POSS'),(9,-30,'SPOS')]:
            normal = self.sim(threshold,kind=kind)['actors'][0]
            extreme = self.sim(threshold-1,kind=kind)['actors'][0]
            self.assertEqual(normal['pose'],prefix+'H')
            self.assertEqual(extreme['pose'],prefix+'M')
            self.assertEqual(extreme['death']['health'],threshold-1)
        self.assertEqual(self.sim(-1000,kind=3002)['actors'][0]['pose'],'SARGI')

    def test_scream_and_fall_happen_on_original_state_entries(self):
        before = self.sim(script='2:0')
        scream = self.sim(script='3:0')
        fall = self.sim(script='8:0')
        self.assertEqual(before['actors'][0]['pose'],'POSSH')
        self.assertEqual(scream['actors'][0]['pose'],'POSSI')
        self.assertTrue(scream['actors'][0]['death']['solid'])
        self.assertEqual(scream['rng'],6)
        self.assertTrue(any('podth3' in e['event'] for e in scream['deathEvents']))
        self.assertEqual(fall['actors'][0]['pose'],'POSSJ')
        self.assertFalse(fall['actors'][0]['death']['solid'])
        self.assertEqual(fall['kills'],1)

    def test_extreme_scream_does_not_draw_random_and_final_frame_persists(self):
        scream = self.sim(-21,'3:0')
        self.assertEqual(scream['rng'],5)
        self.assertTrue(any('slop' in e['event'] for e in scream['deathEvents']))
        for script in ['40:0','100:0']:
            final = self.sim(-21,script)['actors'][0]
            self.assertEqual((final['pose'],final['death']['tics']),('POSSU',-1))
            self.assertFalse(final['death']['solid'])

    def test_demon_falls_later_and_has_no_drop(self):
        self.assertTrue(self.sim(-150,'17:0',3002)['actors'][0]['death']['solid'])
        fall = self.sim(-150,'18:0',3002)
        self.assertFalse(fall['actors'][0]['death']['solid'])
        self.assertEqual(fall['actors'][0]['pose'],'SARGL')
        self.assertEqual(fall['dropped'],[])

    def test_solid_corpse_blocks_then_releases_player_and_drop_is_pickable(self):
        blocked = self.sim(script='7:2')
        passed = self.sim(script='40:2')
        self.assertLessEqual(blocked['x'],12)
        self.assertGreater(passed['x'],64)
        self.assertIn(2,passed['collected'])
        self.assertEqual(passed['ammo'][0],55)  # Original half-clip dropped ammo.

    def test_dead_actor_no_longer_intercepts_bullets(self):
        state = self.sim(script='19:8192',enemies=[(48,0,0,3004,7),(96,0,0,3004,7)])
        self.assertEqual(state['actors'][0]['health'],0)
        self.assertLess(state['actors'][1]['health'],20)
        self.assertEqual(state['kills'],1)

    def test_player_death_flags_weapon_request_and_environment_frag(self):
        state = self.sim(-100,target=-1,enemies=[])
        death = state['playerDeath']
        self.assertEqual((death['health'],death['height'],death['state']),(-100,14,'S_PLAY_DIE1'))
        self.assertFalse(death['solid'])
        self.assertEqual(state['frags'],[1,0,0,0])
        self.assertTrue(any('dropWeapon' in e['event'] for e in state['deathEvents']))
        scream = self.sim(-100,'9:0',target=-1,enemies=[])
        self.assertTrue(any('pldeth' in e['event'] for e in scream['deathEvents']))
        self.assertEqual(self.sim(-101,target=-1,enemies=[])['playerDeath']['state'],'S_PLAY_XDIE1')

    def test_reset_and_script_partitioning(self):
        self.assertEqual(self.sim(-21,'50:0'),self.sim(-21,'4:0,6:0,40:0'))
        reset = self.sim(-21,'50:0,1:1024')
        self.assertIsNone(reset['actors'][0]['death'])
        self.assertIsNone(reset['playerDeath'])
        self.assertEqual((reset['kills'],reset['dropped'],reset['frags']),(0,[],[0,0,0,0]))


if __name__ == '__main__':
    unittest.main()

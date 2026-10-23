"""Imp behavior through the same simulation and renderer used by SDL."""
import json
import struct
import subprocess
import unittest
from pathlib import Path
import test_assets
from test_assets import patch,replace,rgb
from test_combat import arena,combat_art
from test_render import two_rooms
from test_simulation import door_room
from test_things import things,sectors

ROOT=Path(__file__).resolve().parents[1]

def imp_art():
    return (combat_art()+[(f'TROO{chr(65+i)}0',patch([[100+i]*16 for _ in range(56)],8,56)) for i in range(21)]
            +[(f'BAL1{c}0',patch([[245]*12 for _ in range(12)],6,6)) for c in 'ABCDE'])

class ImpTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        output=self.directory/'state.json'
        self.run_cli(['combat','E1M1',script,output],geom)
        return json.loads(output.read_text())

    def test_generated_original_state_table(self):
        subprocess.run(['python3',str(ROOT/'scripts/generate-imp.py')],check=True,capture_output=True)

    def test_map_order_assigns_spawn_randomness_to_the_correct_actor(self):
        # After the player draw (8), a static item takes 109. The imp then
        # receives lastlook=220%4 and duration=1+222%10. Reversing those map
        # entries gives the imp lastlook=109%4 and duration=1+220%10 instead.
        item=(96,64,0,2011,7); imp=(160,0,180,3001,7)
        first=self.state(arena([item,imp]),'0:0')
        second=self.state(arena([imp,item]),'0:0')
        self.assertEqual(first['rng'],second['rng'])
        self.assertEqual(first['actors'][0]['impState'],'442:3:0:0:8:0')
        self.assertEqual(second['actors'][0]['impState'],'442:1:0:0:8:0')

    def test_spawn_countdown_and_original_initial_chase_direction(self):
        geom=arena([(160,0,180,3001,7)])
        self.assertEqual(self.state(geom,'0:0')['actors'][0]['impState'],'442:1:0:0:8:0')
        before=self.state(geom,'10:0')['actors'][0]
        self.assertEqual((before['x'],before['pose']),(160,'TROOB'))
        after=self.state(geom,'11:0')['actors'][0]
        # Original zero-initialized movedir is east even with a westward target.
        self.assertEqual((after['x'],after['impState']),(168,'444:3:0:5:7:0'))

    def test_facing_and_persistent_shot_hearing(self):
        geom=arena([(160,0,0,3001,7)],angle=180)
        asleep=self.state(geom,'120:0')['actors'][0]
        self.assertEqual((asleep['x'],asleep['health']),(160,60))
        self.assertTrue(asleep['mode'].endswith('idle'))
        heard=self.state(geom,'15:8192,39:0')
        self.assertEqual(heard['soundTargets'],[0])
        self.assertEqual(heard['actors'][0]['health'],60) # Fired away from imp.
        self.assertTrue(heard['actors'][0]['mode'].endswith('chase'))

    def test_sound_crosses_open_portal_but_not_closed_portal(self):
        for closed in [False,True]:
            geom=things(sectors(two_rooms(),first=(-16,128),second=(-16,-16 if closed else 128)),[(0,0,180,1,7),(144,0,0,3001,7)])
            state=self.state(geom,'15:8192,39:0')
            self.assertEqual(state['soundTargets'],[0,None] if closed else [0,0])
            self.assertEqual(state['actors'][0]['mode'].endswith('idle'),closed)

    def test_ambush_requires_sight_even_after_hearing(self):
        # REJECT removes sight without closing the sound portal.
        geom=replace(arena([(160,0,0,3001,15)],angle=180),'REJECT',bytes([255]))
        asleep=self.state(geom,'15:8192,39:0')
        self.assertEqual(asleep['soundTargets'],[0])
        self.assertTrue(asleep['actors'][0]['mode'].endswith('idle'))
        ordinary=replace(geom,'THINGS',struct.pack('<5h',0,0,180,1,7)+struct.pack('<5h',160,0,0,3001,7))
        self.assertFalse(self.state(ordinary,'15:8192,39:0')['actors'][0]['mode'].endswith('idle'))

    def test_melee_damage_waits_for_attack_action(self):
        geom=arena([(48,0,180,3001,7)])
        before=self.state(geom,'26:0')
        hit=self.state(geom,'27:0')
        self.assertEqual(before['health'],100)
        self.assertEqual(hit['health'],94)
        self.assertEqual(hit['projectiles'],[])
        self.assertTrue(any('melee 0 6' in e for e in hit['impEvents']))

    def test_fireball_has_travel_time_and_can_be_dodged(self):
        geom=arena([(160,0,180,3001,7)])
        before=self.state(geom,'86:0')
        spawned=self.state(geom,'87:0')
        travelling=self.state(geom,'100:0')
        hit=self.state(geom,'108:0')
        self.assertEqual(before['projectiles'],[])
        self.assertEqual(spawned['health'],100)
        self.assertFalse(spawned['projectiles'][0]['exploding'])
        self.assertEqual(spawned['projectiles'][0]['z'],16) # floor -16 + muzzle 32.
        self.assertEqual(travelling['health'],100)
        self.assertLess(travelling['projectiles'][0]['x'],spawned['projectiles'][0]['x'])
        self.assertEqual(hit['health'],85)
        self.assertTrue(hit['projectiles'][0]['exploding'])
        dodged=self.state(geom,'87:0,21:8')
        self.assertEqual(dodged['health'],100)
        self.assertFalse(dodged['projectiles'][0]['exploding'])

    def test_fireball_wall_explosion_and_removal(self):
        geom=arena([(160,0,180,3001,7)])
        # Dodge and let the already-aimed fireball reach the far wall.
        hit=self.state(geom,'87:0,21:8,30:0')['projectiles'][0]
        gone=self.state(geom,'87:0,21:8,60:0')['projectiles'][0]
        self.assertTrue(hit['exploding'])
        self.assertEqual((hit['momx'],hit['momy'],hit['momz']),(0,0,0))
        self.assertTrue(gone['removed'])

    def test_monster_opens_manual_door_with_original_secret_and_key_gates(self):
        for special in (1,31,32):
            geom=door_room(special,start=(-48,0,0),extras=[(32,0,180,3001,7)])
            result=self.state(geom,'30:0')
            self.assertEqual(result['ceilings'][1]>-16,special==1)
        geom=door_room(1,start=(-48,0,0),extras=[(32,0,180,3001,7)])
        lines=bytearray(dict(geom)['LINEDEFS']);struct.pack_into('<H',lines,2*14+4,4|32)
        self.assertEqual(self.state(replace(geom,'LINEDEFS',bytes(lines)),'30:0')['doors'],[])

    def test_attack_partition_and_reset(self):
        geom=arena([(160,0,180,3001,7)])
        self.assertEqual(self.state(geom,'160:0'),self.state(geom,'10:0,106:0,44:0'))
        self.assertEqual(self.state(geom,'160:0,1:1024'),self.state(geom,'0:0'))

    def test_fireball_is_drawn_fullbright_in_dark_room(self):
        geom=arena([(160,0,180,3001,7)])+imp_art()
        # All shaded colormap rows erase color 245. A fullbright fireball retains it.
        geom=replace(geom,'COLORMAP',bytes(range(256))+bytes(256)*33)
        sector=bytearray(dict(geom)['SECTORS']);struct.pack_into('<h',sector,20,0)
        geom=replace(geom,'SECTORS',bytes(sector))
        output=self.directory/'frame.ppm'
        self.run_cli(['render-combat','E1M1','120:0',output],geom)
        pixels=output.read_bytes().split(b'\n',3)[3]
        self.assertIn(rgb(245),[pixels[i:i+3] for i in range(0,len(pixels),3)])
        for missing in ('BAL1A0','BAL1E0'):
            result=self.run_cli(['render-combat','E1M1','0:0',output],[(n,b) for n,b in geom if n!=missing],ok=False)
            self.assertIn(missing[:5],result.stderr)

if __name__=='__main__':unittest.main()

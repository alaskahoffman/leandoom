"""Combat fixtures drive the same tick, geometry, and renderer as the SDL game."""
import json
import struct
import unittest
import test_assets
from test_assets import artwork, patch, replace, rgb
from test_wad import room, pack
from test_things import things, sectors
from test_render import two_rooms


def arena(enemies=(), size=256, angle=0, extras=()):
    geom = room()
    geom = replace(geom, 'VERTEXES', b''.join(pack('hh',*v) for v in [(-size,-size),(-size,size),(size,size),(size,-size)]))
    # Shooting now uses actual BLOCKMAP actor links. Cover the enlarged arena,
    # sharing a conservative wall list across cells like the small room fixture.
    width=(2*size+127)//128
    count=width*width
    geom=replace(geom,'BLOCKMAP',pack('hhHH',-size,-size,width,width)+pack(f'{count}H',*([4+count]*count))+pack('6H',0,0,1,2,3,65535))
    return things(geom, [(0,0,angle,1,7), *enemies, *extras])


def combat_art(kind=3004, wall_rows=None):
    prefix = {3004:'POSS', 9:'SPOS', 3002:'SARG'}[kind]
    end = 14 if kind == 3002 else 21
    result = artwork(wall_rows)
    result += [(prefix+chr(65+i)+'0',patch([[220+i]*16 for _ in range(64)],8,64)) for i in range(end)]
    result += [('CLIPA0',patch([[200]*8 for _ in range(8)],4,8)), ('SHOTA0',patch([[201]*16 for _ in range(8)],8,8))]
    # Deliberately small fixtures exercise real signed weapon offsets and overlay changes.
    result += [(label,patch([[color]*8 for _ in range(8)],-154,-130)) for label,color in
               [('POL5A0',229),('PISGA0',230),('PISGB0',231),('PISGC0',232),('PISFA0',233),
                ('SHTGA0',234),('SHTGB0',235),('SHTGC0',236),('SHTGD0',237),('SHTFA0',238),('SHTFB0',239),
                ('PUNGA0',240),('PUNGB0',241),('PUNGC0',242),('PUNGD0',243)]]
    return result


class CombatTests(unittest.TestCase):
    setUp = test_assets.AssetTests.setUp
    tearDown = test_assets.AssetTests.tearDown
    run_cli = test_assets.AssetTests.run_cli
    pixel = staticmethod(test_assets.AssetTests.pixel)

    def sim(self, geom, script):
        output = self.directory/'combat.json'
        self.run_cli(['combat','E1M1',script,output],geom)
        return json.loads(output.read_text())

    def frame(self, geom, script):
        output = self.directory/'combat.ppm'
        self.run_cli(['render-combat','E1M1',script,output],geom)
        return output.read_bytes().split(b'\n',3)[3]

    def test_pistol_windup_cadence_release_and_ammo(self):
        geom = arena()
        for tick,shots in [(1,0),(18,0),(19,1),(32,1),(33,2),(47,3)]:
            result = self.sim(geom,f'{tick}:8192')
            self.assertEqual(result['shots'],shots)
            self.assertEqual(result['ammo'][0],50-shots)
        self.assertEqual(self.sim(geom,'15:8192,40:0')['shots'],1)

    def test_out_of_ammo_stops_firing(self):
        result = self.sim(arena(),'1000:8192')
        self.assertEqual(result['ammo'][0],0)
        self.assertEqual(result['shots'],50)

    def test_first_shot_damage_pain_and_enemy_death(self):
        geom = arena([(96,0,0,3004,7),(200,160,0,3004,7)])
        hit = self.sim(geom,'19:8192')
        self.assertEqual(hit['actors'][0]['health'],5)  # Player + two timed actors consume five draws; value 149 gives 15 damage.
        self.assertTrue(hit['actors'][0]['mode'].endswith('pain'))
        dead = self.sim(geom,'34:8192')
        self.assertEqual(dead['actors'][0]['health'],0)
        self.assertEqual(dead['kills'],1)
        self.assertTrue(dead['actors'][0]['mode'].endswith('dying'))
        self.assertEqual(len(dead['dropped']),1)

    def test_nearest_actor_takes_hit_and_order_does_not_change_target(self):
        for enemies in [[(96,0,0,3004,7),(160,0,0,3004,7)],[(160,0,0,3004,7),(96,0,0,3004,7)]]:
            result = self.sim(arena(enemies),'19:8192')
            # Stable THINGS identity survives the hit's immediate knockback.
            target = next(a for a in result['actors'] if enemies[a['thing']-1][0]==96)
            self.assertEqual(target['health'],5)
            self.assertGreater(target['x'],96)
            self.assertEqual([a['health'] for a in result['actors']].count(20),1)

    def test_aim_angle_and_maximum_range(self):
        miss = self.sim(arena([(96,0,180,3004,7)],angle=90),'19:8192')
        self.assertEqual(miss['actors'][0]['health'],20)
        distant = self.sim(arena([(3000,0,180,3004,7)],size=4096),'19:8192')
        self.assertEqual(distant['actors'][0]['health'],20)

    def test_knockback_continues_after_death_and_stops_at_walls(self):
        geom=arena([(96,0,0,3004,7),(200,160,0,3004,7)])
        killed=self.sim(geom,'33:8192')['actors'][0]
        later=self.sim(geom,'33:8192,10:0')['actors'][0]
        self.assertEqual(killed['health'],0)
        self.assertGreater(later['x'],killed['x'])
        self.assertFalse(later['death']['solid']) # A_Fall does not discard momentum.
        wall=arena([(220,0,0,3004,7),(200,160,0,3004,7)])
        for idle in [0,8,16]:
            pushed=self.sim(wall,f'19:8192,{idle}:0')['actors'][0]
            self.assertGreater(pushed['x'],220)
            self.assertLessEqual(pushed['x'],236) # 20-unit radius against x=256.

    def portal(self, ceiling=128, flags=4):
        geom = sectors(two_rooms(), second=(-16,ceiling))
        geom = things(geom,[(0,0,0,1,7),(144,0,180,3004,7)])
        lines = bytearray(dict(geom)['LINEDEFS'])
        struct.pack_into('<H',lines,2*14+4,flags)
        return replace(geom,'LINEDEFS',lines)

    def test_closed_door_blocks_sight_and_low_lintel_blocks_shots(self):
        for ceiling in [-16,0]:
            result = self.sim(self.portal(ceiling),'60:8192')
            self.assertEqual(result['health'],100)
            self.assertEqual(result['actors'][0]['health'],20)
            # A low opening can reveal feet even when these shots hit the wall.
            self.assertEqual(result['actors'][0]['mode'].endswith('idle'),ceiling==-16)
        self.assertEqual(self.sim(self.portal(),'19:8192')['actors'][0]['health'],5)

    def test_block_monsters_line_stops_pursuit_but_not_sight(self):
        result = self.sim(self.portal(flags=6),'180:0')
        self.assertGreaterEqual(result['actors'][0]['x'],84)
        self.assertLess(result['actors'][0]['x'],144)
        self.assertLess(result['health'],100)

    def test_solid_props_absorb_pistol_shots(self):
        result = self.sim(arena([(160,0,180,3004,7)],extras=[(64,0,0,2035,7)]),'19:8192')
        self.assertEqual(result['actors'][0]['health'],20)

    def test_facing_noise_and_ambush(self):
        backwards = arena([(160,0,0,3004,7)],angle=90)
        self.assertTrue(self.sim(backwards,'20:0')['actors'][0]['mode'].endswith('idle'))
        self.assertFalse(self.sim(backwards,'24:8192')['actors'][0]['mode'].endswith('idle'))
        ambush = arena([(160,0,0,3004,15)],angle=90)
        # Ambush requires sight after hearing, not a front-facing player.
        self.assertFalse(self.sim(ambush,'24:8192')['actors'][0]['mode'].endswith('idle'))
        hidden=replace(ambush,'REJECT',bytes([255]))
        self.assertTrue(self.sim(hidden,'24:8192')['actors'][0]['mode'].endswith('idle'))

    def test_enemy_pursues_attacks_and_player_can_die(self):
        geom = arena([(160,0,180,3004,7)])
        early = self.sim(geom,'200:0')
        self.assertLess(early['actors'][0]['x'],160)
        hurt = self.sim(geom,'200:0')
        self.assertLess(hurt['health'],100)
        dead = self.sim(geom,'2000:0')
        self.assertEqual(dead['health'],0)
        self.assertEqual(dead['eye'],dead['feet']+6)
        self.assertIn('died',dead['message'])
        stopped = self.sim(geom,'2000:0,100:8194')
        self.assertEqual(stopped['health'],0)
        self.assertEqual(stopped['shots'],0)
        self.assertEqual((stopped['x'],stopped['y']),(dead['x'],dead['y']))

    def test_shotgunner_and_demon_attacks(self):
        for kind in [9,3002]:
            result = self.sim(arena([(160,0,180,kind,7)]),'150:0')
            self.assertLess(result['health'],100)
            # Damage now pushes the player backward; separation is relative to
            # that live position, rather than the original spawn point.
            self.assertGreaterEqual(result['actors'][0]['x']-result['x'],36 if kind==9 else 46)

    def test_enemy_bullets_can_destroy_blocking_barrels(self):
        geom = arena([(160,0,180,3004,7)],extras=[(40,0,0,2035,7)])
        result = self.sim(geom,'600:0')
        self.assertLess(result['health'],100)
        barrel=next(a for a in result['actors'] if a['kind']==2035)
        self.assertEqual(barrel['health'],0)
        self.assertTrue(barrel['removed'])

    def test_restart_restores_opened_door_and_key(self):
        from test_simulation import door_room
        geom = door_room(32,extras=[(16,0,0,5,7)])
        opened = self.sim(geom,'1:2,1:4096,80:0')
        self.assertEqual(opened['ceilings'][1],124)
        self.assertTrue(opened['blue'])
        reset = self.sim(geom,'1:2,1:4096,80:0,1:1024')
        self.assertEqual(reset,self.sim(geom,'0:0'))

    def test_invulnerability_prevents_damage(self):
        result = self.sim(arena([(96,0,180,3004,7)],extras=[(0,0,0,2022,7)]),'1:2,149:0')
        self.assertEqual(result['health'],100)
        self.assertGreater(result['powers'][0],0)

    def test_armor_reduces_enemy_damage(self):
        enemy = [(96,0,180,3004,7)]
        plain = self.sim(arena(enemy,extras=[(200,200,0,2019,7)]),'1:2,299:0')
        armored = self.sim(arena(enemy,extras=[(0,0,0,2019,7)]),'1:2,299:0')
        self.assertGreater(armored['health'],plain['health'])
        self.assertLess(armored['armor'],200)
        self.assertEqual(armored['rng'],plain['rng'])

    def test_corpses_do_not_block_and_dropped_clip_gives_five(self):
        result = self.sim(arena([(96,0,180,3004,7)]),'33:8192,40:2')
        self.assertEqual(result['kills'],1)
        self.assertGreater(result['x'],120)
        self.assertEqual(result['ammo'][0],53)
        self.assertIn(result['dropped'][0],result['collected'])

    def test_restart_resets_combat_and_geometry(self):
        geom = arena([(96,0,180,3004,7)],extras=[(0,0,0,5,7)])
        fresh = self.sim(geom,'0:0')
        reset = self.sim(geom,'50:8192,20:2,1:1024')
        self.assertEqual(reset,fresh)
        held = self.sim(geom,'50:8192,5:1024')
        self.assertEqual(held['ticks'],4)

    def test_replay_is_repeatable_across_input_segments(self):
        geom = arena([(160,30,180,9,7),(160,-60,180,3002,7)])
        a = self.sim(geom,'40:8192,100:0')
        b = self.sim(geom,'10:8192,30:8192,50:0,50:0')
        self.assertEqual(a,b)

    def test_weapon_offsets_muzzle_flash_and_death_hides_weapon(self):
        geom = arena()+combat_art()
        for script,color in [('15:0',230),('19:8192',233),('26:8192',232)]:
            pixels = self.frame(geom,script)
            self.assertEqual(self.pixel(pixels,156,164),rgb(color))
        geom = arena([(96,0,180,3004,7)])+combat_art()
        dead = self.frame(geom,'2000:0')
        self.assertNotEqual(self.pixel(dead,156,164),rgb(230))
        self.assertFalse(bytes((255,80,60)) in dead)  # The custom death text was removed.

    def test_enemy_uses_pain_and_death_sprites(self):
        geom = arena([(96,0,0,3004,7),(200,160,0,3004,7)])+combat_art()
        idle = self.frame(geom,'0:0')
        pain = self.frame(geom,'19:8192')
        corpse = self.frame(geom,'34:8192,40:0')
        self.assertEqual(self.pixel(idle,160,80),rgb(220))
        self.assertEqual(self.pixel(pain,160,80),rgb(226))
        self.assertIn(rgb(231),corpse)

    def test_missing_combat_assets_fail_explicitly(self):
        geom = arena([(96,0,180,3004,7)])+combat_art()
        for label in ['PISFA0','POSSF0','POSSL0']:
            result = self.run_cli(['render-combat','E1M1','0:0',self.directory/'bad.ppm'],
                                  [(n,b) for n,b in geom if n!=label],ok=False)
            self.assertIn(label[:5],result.stderr)


if __name__=='__main__':
    unittest.main()

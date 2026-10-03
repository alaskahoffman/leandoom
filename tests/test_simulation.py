"""Independent interaction fixtures; scripted commands drive the actual viewer simulation."""
import json
import struct
import unittest
import test_assets
from test_assets import artwork, definitions, patch, replace, rgb
from test_wad import room, pack, name
from test_render import two_rooms
from test_things import things, sectors


def door_room(special=1, start=(16, 0, 0), extras=(), open_door=False, tagged=False):
    geom = sectors(two_rooms(), second=(-16, 124 if open_door else -16))
    geom = things(geom, [(*start, 1, 7), *extras])
    lines = bytearray(dict(geom)["LINEDEFS"])
    struct.pack_into("<HH", lines, 2*14+6, special, 7 if tagged else 0)
    geom = replace(geom, "LINEDEFS", lines)
    sec = bytearray(dict(geom)["SECTORS"])
    struct.pack_into("<H", sec, 26+24, 7)
    return replace(geom, "SECTORS", sec)


def switch_room(special=63, **kwargs):
    geom = door_room(special, tagged=True, **kwargs)
    side = bytearray(dict(geom)["SIDEDEFS"])
    side[4:12] = name("SW1TEST")
    return replace(geom, "SIDEDEFS", side)


class SimulationTests(unittest.TestCase):
    setUp = test_assets.AssetTests.setUp
    tearDown = test_assets.AssetTests.tearDown
    run_cli = test_assets.AssetTests.run_cli
    pixel = staticmethod(test_assets.AssetTests.pixel)

    def sim(self, geom, script):
        output = self.directory / "state.json"
        self.run_cli(["simulate", "E1M1", script, output], geom)
        return json.loads(output.read_text())

    def frame(self, geom, script):
        output = self.directory / "frame.ppm"
        self.run_cli(["render-sim", "E1M1", script, output], geom)
        return output.read_bytes().split(b"\n", 3)[3]

    def test_manual_door_open_wait_close_and_hold_debounce(self):
        geom = door_room()
        self.assertEqual(self.sim(geom, "1:4096")['ceilings'][1], -16)
        self.assertEqual(self.sim(geom, "11:4096")['ceilings'][1], 4)
        top = self.sim(geom, "71:4096")
        self.assertEqual(top['ceilings'][1], 124)
        # T_MovePlane uses a strict overshoot test: equality is still moving.
        self.assertEqual(top['doors'][0]['direction'], 1)
        self.assertEqual(top['doors'][0]['wait'], 0)
        self.assertEqual(self.sim(geom, "72:4096")['doors'][0]['wait'], 150)
        self.assertEqual(self.sim(geom, "222:4096")['ceilings'][1], 124)
        self.assertEqual(self.sim(geom, "223:4096")['ceilings'][1], 122)
        exact = self.sim(geom, "292:4096")
        self.assertEqual(exact['ceilings'][1], -16)
        self.assertTrue(exact['doors'])
        end = self.sim(geom, "293:4096")
        self.assertEqual(end['ceilings'][1], -16)
        self.assertEqual(end['doors'], [])

    def test_reuse_reverses_manual_door(self):
        result = self.sim(door_room(), "1:4096,10:0,1:4096,1:0")
        self.assertEqual(result['ceilings'][1], 4)
        self.assertEqual(result['doors'][0]['direction'], -1)
        result = self.sim(door_room(), "1:4096,10:0,1:4096,1:0,1:4096,1:0")
        self.assertEqual(result['doors'][0]['direction'], 1)

    def test_open_stays_open_and_fast_door_speed(self):
        for special, speed in [(31, 2), (118, 8)]:
            result = self.sim(door_room(special), "1:4096,1:0")
            self.assertEqual(result['ceilings'][1], -16+speed)
            self.assertEqual(result['specials'][2], 0)
            result = self.sim(door_room(special), "1:4096,400:0")
            self.assertEqual(result['ceilings'][1], 124)
            self.assertEqual(result['doors'], [])

    def test_collision_tracks_opening_and_closing_ceiling(self):
        geom = door_room()
        blocked = self.sim(geom, "12:2")
        self.assertLessEqual(float(blocked['x']), 48)
        before = self.sim(geom, "1:4096,27:2")
        self.assertLessEqual(float(before['x']), 48)
        after = self.sim(geom, "1:4096,45:2")
        self.assertGreater(float(after['x']), 80)
        # Player stands in the door sector: the closing door must reopen before crushing.
        protected = self.sim(geom, "1:4096,30:0,20:2,300:0")
        self.assertGreaterEqual(protected['ceilings'][1], 40)
        self.assertTrue(protected['doors'])

    def test_actor_obstructs_door_closure(self):
        geom = door_room(extras=[(110, 0, 0, 3004, 7)])
        result = self.sim(geom, "1:4096,280:0")
        self.assertGreaterEqual(result['ceilings'][1], 40)
        self.assertEqual(result['doors'][0]['direction'], 1)

    def test_use_range_facing_and_back_side(self):
        # The original fine cosine makes the eastward ray slightly shorter
        # than 64 units. Exact range and one unit closer intentionally differ.
        for start in [(-1, 0, 0), (0, 0, 0), (16, 0, 90), (100, 0, 180)]:
            self.assertEqual(self.sim(door_room(start=start), "1:4096,80:0")['ceilings'][1], -16)
        self.assertEqual(self.sim(door_room(start=(1, 0, 0)), "1:4096,80:0")['ceilings'][1], 124)

    def test_use_ray_does_not_cross_solid_wall(self):
        geom = door_room()
        vertices = dict(geom)['VERTEXES'] + pack('4h', 32, 64, 32, -64)
        lines = dict(geom)['LINEDEFS'] + pack('7H', 6, 7, 1, 0, 0, 0, 65535)
        geom = replace(replace(geom, 'VERTEXES', vertices), 'LINEDEFS', lines)
        # Original use tracing respects BLOCKMAP omissions.
        self.assertEqual(self.sim(geom, '1:4096,80:0')['ceilings'][1], 124)
        blockmap = pack('hhHH6H10H', -128, -128, 3, 2, *([10]*6), 0, *range(8), 65535)
        geom = replace(geom, 'BLOCKMAP', blockmap)
        self.assertEqual(self.sim(geom, '1:4096,80:0')['ceilings'][1], -16)

    def test_all_key_colors_cards_and_skulls(self):
        for special, field, card, skull in [(26,'blue',5,40), (28,'red',13,38), (27,'yellow',6,39)]:
            blocked = self.sim(door_room(special), "1:4096,80:0")
            self.assertEqual(blocked['ceilings'][1], -16)
            self.assertIn(field, blocked['message'])
            wrong = self.sim(door_room(special, extras=[(16, 0, 0, 13 if card != 13 else 5, 7)]), "1:4096,80:0")
            self.assertEqual(wrong['ceilings'][1], -16)
            for key in [card, skull]:
                opened = self.sim(door_room(special, extras=[(16, 0, 0, key, 7)]), "1:4098,80:0")
                self.assertTrue(opened[field])
                self.assertEqual(opened['ceilings'][1], 124)
                self.assertEqual(opened['collected'], [1])

    def test_one_shot_switch_changes_texture_and_clears_special(self):
        result = self.sim(switch_room(103), "1:4096,80:0")
        self.assertEqual(result['ceilings'][1], 124)
        self.assertEqual(result['specials'][2], 0)
        self.assertEqual(result['textures'][0][0], 'SW2TEST')

    def test_repeatable_button_resets_after_one_second(self):
        geom = switch_room()
        self.assertEqual(self.sim(geom, "1:4096,34:0")['textures'][0][0], 'SW2TEST')
        result = self.sim(geom, "1:4096,35:0")
        self.assertEqual(result['textures'][0][0], 'SW1TEST')
        self.assertEqual(result['specials'][2], 63)

    def test_locked_tagged_switch_and_close_only_switch(self):
        for special, field, key in [(133, 'blue', 5), (135, 'red', 13), (137, 'yellow', 6)]:
            self.assertEqual(self.sim(switch_room(special), "1:4096,80:0")['ceilings'][1], -16)
            result = self.sim(switch_room(special, extras=[(16, 0, 0, key, 7)]), "1:4098,30:0")
            self.assertTrue(result[field])
            self.assertEqual(result['ceilings'][1], 124)
        result = self.sim(switch_room(50, open_door=True), "1:4096,80:0")
        self.assertEqual(result['ceilings'][1], -16)

    def test_switch_artwork_changes_in_rendered_frame(self):
        geom = switch_room(103)
        names = ('SW1TEST','SW2TEST','NEARWALL','FARWALL','UPPER','LOWER')
        art = artwork([[7]*8 for _ in range(128)], names, ('FLOOR_A','FLOOR_B','CEILING'))
        art = replace(art,'PNAMES',pack('I',3)+name('BASE')+name('OFF')+name('ON'))
        defs = [(label,8,128,[(0,0,1 if label=='SW1TEST' else 2 if label=='SW2TEST' else 0)]) for label in names]
        art = replace(art,'TEXTURE1',definitions(defs))
        art += [('OFF',patch([[230]*8 for _ in range(128)])),('ON',patch([[240]*8 for _ in range(128)]))]
        self.assertEqual(self.pixel(self.frame(geom+art,'0:0'),160,100),rgb(230))
        self.assertEqual(self.pixel(self.frame(geom+art,'1:4096'),160,100),rgb(240))
        self.assertNotEqual(self.frame(geom+art,'1:4096'),self.frame(geom+art,'1:4096,70:0'))

    def test_missing_switch_partner_reports_error(self):
        geom = switch_room(103)
        art = artwork(texture_names=('SW1TEST','NEARWALL','FARWALL','LOWER'), flats=('FLOOR_A','FLOOR_B','CEILING'))
        result = self.run_cli(['render-sim','E1M1','1:4096',self.directory/'bad.ppm'],geom+art,ok=False)
        self.assertIn('SW2TEST',result.stderr)

    def test_no_target_does_not_consume_switch(self):
        geom = switch_room(103)
        lines = bytearray(dict(geom)['LINEDEFS'])
        struct.pack_into('<H', lines, 2*14+8, 999)
        result = self.sim(replace(geom, 'LINEDEFS', lines), '1:4096')
        self.assertEqual(result['specials'][2], 103)
        self.assertEqual(result['textures'][0][0], 'SW1TEST')

    def pickups(self, kinds):
        return things(room(), [(0, 0, 0, 1, 7)] + [(0, 0, 0, k, 7) for k in kinds])

    def test_health_armor_caps_and_unused_medikits(self):
        result = self.sim(self.pickups([2011, 2012, 2014, 2013, 2019, 2018, 2015]), '1:2,9:0')
        self.assertEqual((result['health'], result['armor'], result['armorType']), (200, 200, 2))
        self.assertEqual(result['collected'], [7, 6, 5, 4, 3])

    def test_ammo_caps_backpack_and_weapons(self):
        result = self.sim(self.pickups([2048]*4+[2049]*3+[2046]*11+[17]*4), '1:2')
        self.assertEqual(result['ammo'], [200, 50, 50, 300])
        self.assertEqual(len(result['collected']), 3+3+10+3)
        result = self.sim(self.pickups([2048]*9+[2049]*6+[2046]*21+[17]*7+[8]), '1:2')
        self.assertEqual(result['ammo'], [400, 100, 100, 600])
        self.assertTrue(result['backpack'])
        result = self.sim(self.pickups([2001,2002,2003,2004,2006,2005,82]), '1:2')
        self.assertEqual(result['weapons'], list(range(9)))
        self.assertEqual(result['ammo'], [70, 16, 2, 80])

    def test_powerup_inventory_and_timers(self):
        result = self.sim(self.pickups([2022,2023,2024,2025,2045,2026]), '1:2,35:0')
        self.assertEqual(result['powers'], [1015,2065,2065,4165])
        self.assertTrue(result['berserk'])
        self.assertTrue(result['computerMap'])

    def test_counter_stage_precedes_pickup_and_preserves_berserk_age(self):
        geom = self.pickups([2022,2023,2024,2025,2045])
        first = self.sim(geom, '1:2')
        self.assertEqual(first['powers'], [1050,2100,2100,4200])
        self.assertEqual(first['fixedColormap'], 0)  # Effect selection ran before touch.
        self.assertEqual(first['strengthTics'], 1)
        self.assertEqual(first['pickupBonus'], 30)
        self.assertTrue(first['shadow'])
        later = self.sim(geom, '1:2,35:0')
        self.assertEqual(later['strengthTics'], 36)
        self.assertEqual(later['pickupBonus'], 0)
        self.assertEqual(later['fixedColormap'], 32)

    def test_invisibility_expiry_and_colormap_blink_priority(self):
        geom = self.pickups([2022,2024,2045])
        for ticks, invulnerability, fixed in [(922,129,32),(923,128,0),(931,120,32),
                                             (932,119,0),(1050,1,0),(1051,0,1)]:
            with self.subTest(ticks=ticks):
                state = self.sim(geom, f'1:2,{ticks-1}:0')
                self.assertEqual(state['powers'][0], invulnerability)
                self.assertEqual(state['fixedColormap'], fixed)
        before = self.sim(geom, '1:2,2099:0')
        after = self.sim(geom, '1:2,2100:0')
        self.assertEqual(before['powers'][1], 1)
        self.assertTrue(before['shadow'])
        self.assertEqual(after['powers'][1], 0)
        self.assertFalse(after['shadow'])

    def test_idle_does_not_touch_and_contact_is_square(self):
        geom = things(room(), [(0,0,0,1,7),(35,35,0,2007,7)])
        self.assertEqual(self.sim(geom, '20:0')['collected'], [])
        result = self.sim(geom, '1:2,20:0')
        self.assertEqual(result['collected'], [1])
        self.assertEqual(result['ammo'][0], 60)  # Removed item cannot be granted twice.
        self.assertEqual(result['message'], 'Picked up a clip.')

    def test_pickup_survives_blocked_move_but_respects_height(self):
        geom = sectors(door_room(extras=[(70,0,0,5,7)], start=(48,0,0)), second=(0,0))
        result = self.sim(geom, '1:2')
        self.assertTrue(result['blue'])
        self.assertEqual(result['x'], 48)  # Closed portal rejects the move after touch.
        self.assertEqual(result['collected'], [1])
        geom = sectors(geom, second=(80,128))
        self.assertFalse(self.sim(geom, '1:2')['blue'])

    def test_card_skull_counters_and_pending_weapon_survive_ticks(self):
        result = self.sim(self.pickups([5,40,2014,2025,2001]), '1:2,20:0')
        self.assertEqual(result['cards'], [True,False,False,True,False,False])
        self.assertEqual(result['pendingWeapon'], 2)
        self.assertEqual(result['itemCount'], 1)  # Suit has no MF_COUNTITEM.
        self.assertEqual(result['collected'], [5,4,3,2,1])
        self.assertEqual(result['ammo'], [50,8,0,0])

    def test_collected_sprite_disappears(self):
        geom = things(room(), [(0,0,0,1,7), (30,0,0,2007,7)]) + artwork()
        geom += [('CLIPA0',patch([[240]*16 for _ in range(64)],8,64))]
        before = self.frame(geom, '0:0')
        after = self.frame(geom, '1:2')
        self.assertEqual(self.pixel(before,160,100), rgb(240))
        self.assertNotEqual(self.pixel(after,160,100), rgb(240))

    def test_idle_frames_follow_tics_and_cycle(self):
        geom = things(room(), [(0,0,0,1,7), (48,0,0,3004,7)]) + artwork()
        geom += [('POSSA0',patch([[230]*16 for _ in range(64)],8,64)),
                 ('POSSB0',patch([[240]*16 for _ in range(64)],8,64))]
        for tick, color in [(0,230),(9,230),(10,240),(19,240),(20,230),(30,240)]:
            self.assertEqual(self.pixel(self.frame(geom, f'{tick}:0'),160,100),rgb(color))

    def test_animated_fullbright_and_unequal_durations(self):
        geom = things(room(), [(0,0,0,1,7), (48,0,0,2018,7)]) + artwork()
        geom = replace(geom, 'COLORMAP', bytes(range(256)) + bytes([17])*(33*256))
        geom += [('ARM1A0',patch([[230]*16 for _ in range(64)],8,64)),
                 ('ARM1B0',patch([[240]*16 for _ in range(64)],8,64))]
        for tick, color in [(0,17),(5,17),(6,240),(12,240),(13,17)]:
            self.assertEqual(self.pixel(self.frame(geom, f'{tick}:0'),160,100),rgb(color))

    def test_sprite_namespace_excludes_intermission_name_collision(self):
        geom = things(room(), [(0,0,0,1,7), (48,0,0,3003,7)]) + artwork()
        sprites = [('BOSSA0',patch([[230]*16 for _ in range(64)],8,64)),
                   ('BOSSB0',patch([[240]*16 for _ in range(64)],8,64))]
        for extra in [[('S_START',b''),*sprites,('S_END',b''),('BOSSBACK',b'not a sprite')],
                      [*sprites,('BOSSBACK',b'not a sprite')]]:
            self.assertEqual(self.pixel(self.frame(geom+extra,'10:0'),160,100),rgb(240))

    def test_sprite_namespace_still_accepts_standalone_patch_override(self):
        geom = things(room(), [(0,0,0,1,7), (48,0,0,3003,7)]) + artwork()
        geom += [('S_START',b''), ('BOSSA0',patch([[230]*16 for _ in range(64)],8,64)),
                 ('BOSSB0',patch([[240]*16 for _ in range(64)],8,64)), ('S_END',b'')]
        output = self.directory/'override.ppm'
        self.run_cli(['render-sim','E1M1','10:0',output],geom,
                     [[('BOSSB0',patch([[220]*16 for _ in range(64)],8,64))]])
        self.assertEqual(self.pixel(output.read_bytes().split(b'\n',3)[3],160,100),rgb(220))

    def test_missing_animation_frame_is_an_error(self):
        geom = things(room(), [(0,0,0,1,7), (48,0,0,3004,7)]) + artwork()
        geom += [('POSSA0',patch([[230]]))]
        result = self.run_cli(['render-sim','E1M1','10:0',self.directory/'bad.ppm'],geom,ok=False)
        self.assertIn('POSSB',result.stderr)

    def test_script_validation_and_repeatability(self):
        for script in ['bad','1:x','10001:0','1:9000','-1:0','9999:0,2:0']:
            self.run_cli(['simulate','E1M1',script,self.directory/'bad.json'],room(),ok=False)
        geom = switch_room(29)
        a = self.sim(geom, '1:4096,35:0,12:2')
        b = self.sim(geom, '1:4096,10:0,25:0,12:2')
        self.assertEqual(a,b)


if __name__ == '__main__':
    unittest.main()

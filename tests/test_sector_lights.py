"""Sector-special effects through WAD decoding, simulation and indexed rendering."""
import json
import struct
import unittest
import test_assets
from test_assets import artwork, replace
from test_render import two_rooms
from test_combat import arena
from test_wad import pack


def sectors(geom,values):
    data=bytearray(dict(geom)['SECTORS'])
    for i,(light,special) in enumerate(values):
        struct.pack_into('<hH',data,26*i+20,light,special)
    return replace(geom,'SECTORS',bytes(data))


def scene(special,light=128,other=64):
    return sectors(two_rooms(),[(light,special),(other,0)])


def crossing_scene(special,sector_special=0,blocked=False,reverse=False,tag=7):
    geom=scene(sector_special)
    data=bytearray(dict(geom)['SECTORS'])
    for i in range(2): struct.pack_into('<hh',data,26*i,0,128)
    if blocked: struct.pack_into('<h',data,28,32)
    struct.pack_into('<H',data,24,tag)
    geom=replace(geom,'SECTORS',bytes(data))
    lines=bytearray(dict(geom)['LINEDEFS'])
    struct.pack_into('<HH',lines,2*14+6,special,tag)
    geom=replace(geom,'LINEDEFS',bytes(lines))
    if reverse:
        data=bytearray(dict(geom)['THINGS']);struct.pack_into('<hhH',data,0,128,0,180)
        geom=replace(geom,'THINGS',bytes(data))
    return geom


class SectorLightTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    pixel=staticmethod(test_assets.AssetTests.pixel)

    def state(self,geom,script,combat=False):
        path=self.directory/'lights.json'
        self.run_cli(['combat' if combat else 'simulate','E1M1',script,path],geom)
        return json.loads(path.read_text())

    def frame(self,geom,script):
        path=self.directory/'lights.ppm'
        self.run_cli(['render-sim','E1M1',script,path],geom)
        return path.read_bytes().split(b'\n',3)[3]

    def test_original_glow_reverses_before_endpoints(self):
        for tic,light,direction in [(0,128,-1),(1,120,-1),(7,72,-1),(8,72,1),(14,120,1),(15,120,-1),(16,112,-1)]:
            result=self.state(scene(8),f'{tic}:0')
            self.assertEqual(result['sectorLights'],[light,64])
            self.assertEqual(result['lightThinkers'][0]['direction'],direction)
            self.assertEqual(result['rng'],1) # Player P_SpawnMobj lastlook.

    def test_flash_countdown_uses_bitmask_not_modulo_and_only_draws_when_due(self):
        for tic,light,count,rng in [(0,128,65,2),(64,128,1,2),(65,64,5,3),(69,64,1,3),(70,128,65,4)]:
            result=self.state(scene(1),f'{tic}:0')
            self.assertEqual(result['sectorLights'][0],light)
            self.assertEqual(result['lightThinkers'][0]['count'],count)
            self.assertEqual(result['rng'],rng)

    def test_strobes_keep_original_periods_sync_and_damage_marker(self):
        for special,dark,sync in [(2,15,False),(3,35,False),(4,15,False),(12,35,True),(13,15,True)]:
            first=1 if sync else 6 # (P_Random() & 7) + 1 after the player spawn.
            for tic,light in [(0,128),(first,64),(first+dark-1,64),(first+dark,128),(first+dark+4,128),(first+dark+5,64)]:
                result=self.state(scene(special),f'{tic}:0')
                self.assertEqual(result['sectorLights'][0],light)
                self.assertEqual(result['sectorSpecials'][0],4 if special==4 else 0)
                self.assertEqual(result['rng'],1 if sync else 2)

    def test_fire_uses_current_level_and_retains_minimum_plus_sixteen_quirk(self):
        for tic,light,rng in [(3,128,1),(4,112,2),(7,112,2),(8,128,3),(12,96,4),(16,112,5)]:
            result=self.state(scene(17),f'{tic}:0')
            self.assertEqual(result['sectorLights'][0],light)
            self.assertEqual(result['rng'],rng)
        result=self.state(sectors(arena(),[(128,17)]),'4:0')
        self.assertEqual(result['sectorLights'],[144]) # No invented clamp to maximum.

    def test_neighbor_search_ignores_one_sided_back_sector(self):
        geom=scene(12)
        lines=bytearray(dict(geom)['LINEDEFS']);struct.pack_into('<H',lines,2*14+4,0)
        result=self.state(replace(geom,'LINEDEFS',bytes(lines)),'1:0')
        self.assertEqual(result['lightThinkers'][0]['min'],0)
        self.assertEqual(result['sectorLights'],[0,64])
        self.assertEqual(self.state(geom,'1:0')['sectorLights'],[64,64])

    def test_renderer_uses_changed_sector_table_but_does_not_advance_thinker(self):
        art=artwork([[100]*8 for _ in range(128)],('NEARWALL','FARWALL','UPPER','LOWER'),('FLOOR_A','FLOOR_B','CEILING'))
        # Encode selected colormap row directly so test observes world lighting.
        art=replace(art,'COLORMAP',b''.join(bytes([row])*256 for row in range(34)))
        geom=two_rooms()
        starts=bytearray(dict(geom)['THINGS']);struct.pack_into('<H',starts,4,180)
        geom=replace(geom,'THINGS',bytes(starts))
        animated=sectors(geom,[(128,12),(64,0)])+art
        bright=self.frame(animated,'0:0')
        dark=self.frame(animated,'1:0')
        self.assertNotEqual(self.pixel(bright,10,80),self.pixel(dark,10,80))
        self.assertEqual(dark,self.frame(sectors(geom,[(64,0),(64,0)])+art,'1:0'))
        self.assertEqual(dark,self.frame(animated,'1:0'))
        self.assertEqual(bright,self.frame(animated,'0:0'))

    def test_lighting_and_pistol_share_gameplay_rng_while_pitch_uses_misc(self):
        geom=sectors(arena(),[(128,1)])
        result=self.state(geom,'19:8192',combat=True)
        self.assertEqual(result['shots'],1)
        self.assertEqual(result['rng'],7) # Player, flash, pistol damage, four puff draws.
        self.assertEqual(result['miscRng'],20)
        passive=self.state(geom,'19:0')
        self.assertEqual(passive['rng'],2)
        self.assertEqual(passive['miscRng'],0)

    def test_restart_recreates_thinkers_rng_and_sector_specials(self):
        geom=sectors(two_rooms(),[(128,4),(64,17)])
        initial=self.state(geom,'0:0',combat=True)
        restarted=self.state(geom,'123:0,1:1024',combat=True)
        self.assertEqual(initial,restarted)
        self.assertEqual(self.state(geom,'90:0',combat=True),self.state(geom,'40:0,50:0',combat=True))

    def test_nonlighting_specials_are_preserved_at_spawn(self):
        for special in (0,5,7,9,10,11,14,16):
            geom=sectors(arena(),[(128,special)])
            self.assertEqual(self.state(geom,'0:0')['sectorSpecials'],[special])
            result=self.state(geom,'35:0')
            self.assertEqual(result['sectorLights'],[128])
            # Discovery consumes secrets; lighting must not create a thinker
            # or advance the RNG for this non-lighting special.
            self.assertEqual(result['sectorSpecials'],[0 if special==9 else special])
            self.assertEqual(result['secrets'],1 if special==9 else 0)
            self.assertEqual(result['lightThinkers'],[])
            self.assertEqual(result['rng'],1) # Player P_SpawnMobj lastlook.

    def test_walkover_light_actions_both_directions_and_one_shot_flags(self):
        for special,light,retained in [(12,64,0),(13,255,0),(35,35,0),(104,64,0),
                                       (79,35,79),(80,64,80),(81,255,81)]:
            for reverse in (False,True):
                with self.subTest(special=special,reverse=reverse):
                    result=self.state(crossing_scene(special,reverse=reverse),'20:2')
                    self.assertEqual(result['sectorLights'],[light,64])
                    self.assertEqual(result['specials'][2],retained)
                    self.assertEqual(result['rng'],1) # Player P_SpawnMobj lastlook.

    def test_touch_failed_move_and_use_do_not_activate_walkover_lights(self):
        geom=crossing_scene(35)
        for script in ('14:2','20:4096','5:2,10:4096'):
            result=self.state(geom,script)
            self.assertLess(result['x'],64)
            self.assertEqual(result['sectorLights'],[128,64])
            self.assertEqual(result['specials'][2],35)
        result=self.state(crossing_scene(35,blocked=True),'60:2')
        self.assertLess(result['x'],64)
        self.assertEqual(result['sectorLights'],[128,64])
        self.assertEqual(result['specials'][2],35)

    def test_strobe_starts_on_crossing_and_ticks_in_same_tic(self):
        geom=crossing_scene(17)
        before=self.state(geom,'15:2')
        self.assertLess(before['x'],64)
        self.assertEqual(before['lightThinkers'],[])
        after=self.state(geom,'16:2')
        self.assertGreater(after['x'],64)
        self.assertEqual(after['rng'],2)
        self.assertEqual(after['sectorLights'],[128,64])
        self.assertEqual(after['lightThinkers'][0]['count'],5)
        self.assertEqual(after['specials'][2],0)
        again=self.state(geom,'20:2,30:4')
        self.assertLess(again['x'],64)
        self.assertEqual(len(again['lightThinkers']),1)
        self.assertEqual(again['rng'],2)

    def test_strobe_does_not_replace_existing_light_or_own_specialdata(self):
        result=self.state(crossing_scene(17,sector_special=4),'16:2')
        self.assertEqual(len(result['lightThinkers']),2)
        self.assertEqual([t['dark'] for t in result['lightThinkers']],[15,35])
        self.assertEqual(result['rng'],3)
        self.assertEqual(result['sectorSpecials'][0],0)

    def test_repeatable_light_reapplies_after_existing_glow_overwrites_it(self):
        repeat=self.state(crossing_scene(81,sector_special=8),'20:2,30:4')
        once=self.state(crossing_scene(13,sector_special=8),'20:2,30:4')
        self.assertLess(repeat['x'],64)
        self.assertNotEqual(repeat['sectorLights'],once['sectorLights'])
        self.assertEqual(repeat['specials'][2],81)
        self.assertEqual(once['specials'][2],0)

    def test_tag_zero_includes_all_zero_tag_sectors(self):
        result=self.state(crossing_scene(13,tag=0),'20:2')
        self.assertEqual(result['sectorLights'],[255,255])

    def test_simultaneous_crossings_follow_reverse_contact_order(self):
        # Two coincident walkover lines, both in the blockmap. Original spechit
        # traversal visits line 7 (255) then line 2 (35), clearing both at once.
        geom=crossing_scene(35)
        lines=dict(geom)['LINEDEFS']
        extra=bytearray(lines[28:42]);struct.pack_into('<H',extra,6,13)
        geom=replace(geom,'LINEDEFS',lines+bytes(extra))
        blockmap=pack('hhHH6H10H',-128,-128,3,2,*([10]*6),0,*range(8),65535)
        geom=replace(geom,'BLOCKMAP',blockmap)
        result=self.state(geom,'16:2')
        self.assertEqual(result['sectorLights'],[35,64])
        self.assertEqual(result['specials'],[0]*8)

    def test_trigger_restart_and_script_partition_are_deterministic(self):
        geom=crossing_scene(17)
        self.assertEqual(self.state(geom,'0:0',True),self.state(geom,'20:2,1:1024',True))
        self.assertEqual(self.state(geom,'20:2',True),self.state(geom,'15:2,1:2,4:2',True))

    def test_trigger_changes_rendered_colormap(self):
        art=artwork([[100]*8 for _ in range(8)],('NEARWALL','FARWALL','UPPER','LOWER'),('FLOOR_A','FLOOR_B','CEILING'))
        art=replace(art,'COLORMAP',b''.join(bytes([row])*256 for row in range(34)))
        triggered=crossing_scene(35,tag=0)
        baseline=crossing_scene(0,tag=0)
        dark=sectors(baseline,[(35,0),(35,0)])
        frame=self.frame(triggered+art,'20:2')
        self.assertEqual(frame,self.frame(dark+art,'20:2'))
        self.assertNotEqual(frame,self.frame(baseline+art,'20:2'))

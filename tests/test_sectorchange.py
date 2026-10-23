"""Sector-change integration through moving doors, combat state, and rendering."""
import json
import unittest
import test_assets
from test_assets import artwork,patch,replace
from test_combat import combat_art
from test_simulation import door_room,switch_room
from test_things import sectors


class SectorChangeTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script,combat=False):
        output=self.directory/'sector.json'
        self.run_cli(['combat' if combat else 'simulate','E1M1',script,output],geom)
        return json.loads(output.read_text())

    def test_scan_includes_player_in_expanded_block_even_away_from_door(self):
        # Player is 48 units from the portal, outside the old radius test.
        geom=door_room(start=(16,0,0),extras=[(16,0,0,2007,7)])
        self.assertEqual(self.state(geom,'0:0')['collected'],[])
        result=self.state(geom,'1:4096')
        self.assertEqual(result['x'],16)
        self.assertEqual(result['collected'],[1])
        self.assertEqual(result['ammo'][0],60)

    def test_shootable_barrel_blocks_but_solid_decoration_does_not(self):
        for kind,ceiling in ((30,-16),(2035,26)):
            with self.subTest(kind=kind):
                geom=switch_room(50,open_door=True,extras=[(110,0,0,kind,7)])
                result=self.state(geom,'1:4096,100:0')
                self.assertEqual(result['ceilings'][1],ceiling)
                self.assertEqual(result['gibbed'],[])
                self.assertEqual(bool(result['doors']),kind==2035)

    def test_map_corpse_decoration_retains_original_positive_spawn_health(self):
        geom=switch_room(50,open_door=True,extras=[(110,0,0,18,7)])
        result=self.state(geom,'1:4096,100:0')
        self.assertEqual(result['ceilings'][1],-16)
        self.assertEqual(result['gibbed'],[])
        self.assertEqual(result['crushedDrops'],[])

    def death_room(self):
        # Start slightly below the target so the existing activation adapter
        # creates a normal door thinker; original activation is a later port.
        # Face away so the target stays inside the door during weapon raising.
        return sectors(door_room(open_door=True,extras=[(110,0,0,3004,7)]),second=(-16,122))

    def test_dead_enemy_gibs_and_drop_is_removed_without_a_pickup(self):
        geom=self.death_room()
        before=self.state(geom,'65:8192',True)
        self.assertEqual(before['kills'],1)
        self.assertEqual(before['gibbed'],[])
        self.assertEqual(before['dropped'],[2])
        script='65:8192,1:4096,300:0'
        result=self.state(geom,script,True)
        self.assertEqual(result['ceilings'][1],-16)
        self.assertEqual(result['doors'],[])
        self.assertEqual(result['gibbed'],[1])
        corpse=result['actors'][0]['death']
        self.assertEqual((corpse['state'],corpse['tics'],corpse['height'],corpse['solid']),
                         ('S_GIBS',-1,0,False))
        self.assertEqual(corpse['health'],before['actors'][0]['death']['health'])
        self.assertEqual(result['crushedDrops'],[2])
        self.assertEqual(result['collected'],[])
        self.assertEqual(result['ammo'],before['ammo'])
        self.assertEqual(result,self.state(geom,'65:8192,1:4096,150:0,150:0',True))
        self.assertEqual(self.state(geom,'0:0',True),self.state(geom,script+',1:1024',True))

    def test_gib_sprite_is_loaded_and_drawn_after_reopening(self):
        geom=self.death_room()
        script='65:8192,1:4096,300:0,1:4096,80:0'
        state=self.state(geom,script,True)
        self.assertEqual(state['gibbed'],[1])
        self.assertEqual(state['crushedDrops'],[2])
        self.assertEqual(state['ceilings'][1],124)
        art=combat_art()
        for label,payload in artwork(texture_names=('NEARWALL','FARWALL','UPPER','LOWER'),flats=('FLOOR_A','FLOOR_B','CEILING')):
            if label in dict(art):art=replace(art,label,payload)
            else:art.append((label,payload))
        frames=[]
        for color in (228,229):
            output=self.directory/f'gib-{color}.ppm'
            lumps=replace(art,'POL5A0',patch([[color]*16 for _ in range(8)],8,8))+geom
            self.run_cli(['render-combat','E1M1',script,output],lumps)
            frames.append(output.read_bytes())
        self.assertNotEqual(*frames)

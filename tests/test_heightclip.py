"""The door adapter must retain real position-query effects during clipping."""
import json
import struct
import unittest
import test_assets
from test_assets import replace
from test_simulation import door_room, switch_room


class HeightClipTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        path=self.directory/'heightclip.json'
        self.run_cli(['simulate','E1M1',script,path],geom)
        return json.loads(path.read_text())

    def test_door_height_query_can_collect_without_player_xy_movement(self):
        geom=door_room(start=(49,0,0),extras=[(49,0,0,2007,7)])
        before=self.state(geom,'0:0')
        self.assertEqual(before['collected'],[])
        after=self.state(geom,'1:4096')
        self.assertEqual(after['x'],49)
        self.assertEqual(after['collected'],[1])
        self.assertEqual(after['ammo'][0],60)
        self.assertEqual(self.state(geom,'1:4096,100:0')['collected'],[1])

    def test_monster_blocking_line_can_leave_early_query_heights_unchanged(self):
        # One unit inside original fine-angle use range; test the height query,
        # independently of the exact 64-unit use boundary.
        geom=switch_room(50,open_door=True,start=(1,0,0),extras=[(49,0,0,3004,7)])
        ordinary=self.state(geom,'1:4096,100:0')
        self.assertEqual(ordinary['ceilings'][1],40)
        self.assertTrue(ordinary['doors'])
        lines=bytearray(dict(geom)['LINEDEFS']);struct.pack_into('<H',lines,2*14+4,6)
        blocked=self.state(replace(geom,'LINEDEFS',bytes(lines)),'1:4096,100:0')
        self.assertEqual(blocked['ceilings'][1],-16)
        self.assertEqual(blocked['doors'],[])

    def test_blocked_closure_and_repeated_queries_preserve_pickup_once(self):
        geom=switch_room(50,open_door=True,start=(49,0,0),extras=[(49,0,0,2007,7)])
        result=self.state(geom,'1:4096,100:0')
        self.assertEqual(result['ceilings'][1],40)
        self.assertEqual(result['doors'][0]['direction'],-1)
        self.assertEqual(result['collected'],[1])
        self.assertEqual(result['ammo'][0],60)

    def test_clipping_effects_survive_script_partition_and_reset(self):
        geom=door_room(start=(49,0,0),extras=[(49,0,0,2007,7)])
        self.assertEqual(self.state(geom,'1:4096,100:0'),self.state(geom,'1:4096,1:0,99:0'))
        self.assertEqual(self.state(geom,'0:0'),self.state(geom,'1:4096,100:0,1:1024'))

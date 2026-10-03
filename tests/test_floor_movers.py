"""E1M1 movers through real WAD crossings, clipping, pickup and restart paths."""
import json
import struct
import unittest
import test_assets
from test_assets import replace
from test_render import two_rooms
from test_things import sectors,things
from test_simulation import door_room
from test_wad import pack


def extra_trigger(geom,x,special,tag,side):
    vertices=dict(geom)['VERTEXES'];n=len(vertices)//4
    lines=dict(geom)['LINEDEFS'];count=len(lines)//14
    geom=replace(geom,'VERTEXES',vertices+pack('4h',x,64,x,-64))
    geom=replace(geom,'LINEDEFS',lines+pack('7H',n,n+1,4,special,tag,side,side))
    return replace(geom,'BLOCKMAP',pack('hhHH6H',-128,-128,3,2,*([10]*6))+pack('H',0)+b''.join(pack('H',i) for i in range(count+1))+pack('H',65535))


def mover_room(special=88,low=-32,interior=False):
    geom=sectors(two_rooms(),first=(low,128),second=(0,128))
    geom=things(geom,[(112,0,0,1,7)] if interior else [(80,0,180,1,7)])
    sec=bytearray(dict(geom)['SECTORS']);struct.pack_into('<H',sec,50,7)
    geom=replace(geom,'SECTORS',bytes(sec))
    if interior:return extra_trigger(geom,128,special,7,1)
    lines=bytearray(dict(geom)['LINEDEFS']);struct.pack_into('<HH',lines,34,special,7)
    return replace(geom,'LINEDEFS',bytes(lines))


class FloorMoverTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        path=self.directory/'mover.json'
        self.run_cli(['simulate','E1M1',script,path],geom)
        return json.loads(path.read_text())

    def test_turbo_crossing_moves_same_tic_and_clears_once(self):
        geom=mover_room(36)
        before=self.state(geom,'6:2')
        self.assertEqual(before['floors'],[-32,0])
        first=self.state(geom,'7:2')
        self.assertEqual(first['floors'],[-32,-4])
        self.assertEqual(first['specials'][2],0)
        exact=self.state(geom,'7:2,5:0')
        self.assertEqual(exact['floors'][1],-24)
        self.assertTrue(exact['floorMovers'])
        end=self.state(geom,'7:2,6:0')
        self.assertEqual(end['floorMovers'],[])
        self.assertEqual([s['sound'].split('.')[-1] for s in end['moverSounds']],['stop'])

    def test_lift_exact_endpoints_wait_and_removal(self):
        geom=mover_room()
        for tic,floor,status,count in [(14,-32,'down',0),(15,-32,'waiting',105),(119,-32,'waiting',1),(120,-32,'up',0),(121,-28,'up',0),(128,0,'up',0),(129,0,None,None)]:
            with self.subTest(tic=tic):
                result=self.state(geom,f'7:2,{tic-7}:0')
                self.assertEqual(result['floors'][1],floor)
                self.assertEqual(result['specials'][2],88)
                if status:
                    self.assertEqual(result['floorMovers'][0]['status'].split('.')[-1],status)
                    self.assertEqual(result['floorMovers'][0]['count'],count)
                else:self.assertEqual(result['floorMovers'],[])

    def test_player_rides_platform_down_and_back_up(self):
        geom=mover_room(interior=True)
        for script,floor in [('20:2,30:0',-32),('20:2,160:0',0)]:
            result=self.state(geom,script)
            self.assertGreater(result['x'],80)
            self.assertEqual(result['floors'][1],floor)
            self.assertEqual(result['feet'],floor)
            self.assertEqual(result['health'],100)

    def test_lift_retriggers_from_reverse_crossing_after_completion(self):
        geom=mover_room(low=-16)
        end=self.state(geom,'10:2,170:0')
        self.assertEqual(end['floorMovers'],[])
        again=self.state(geom,'10:2,170:0,40:4')
        self.assertTrue(again['floorMovers'])
        self.assertEqual(again['specials'][2],88)

    def test_busy_door_suppresses_floor_but_one_shot_is_consumed(self):
        geom=extra_trigger(door_room(start=(48,0,0)),32,36,7,0)
        result=self.state(geom,'1:4096,10:4')
        self.assertTrue(result['doors'])
        self.assertEqual(result['floorMovers'],[])
        self.assertEqual(result['specials'][-1],0)

    def test_lift_obstruction_reverses_without_damaging_rider(self):
        geom=sectors(two_rooms(),first=(0,128),second=(64,104))
        geom=things(geom,[(-16,0,0,1,7)])
        sec=bytearray(dict(geom)['SECTORS']);struct.pack_into('<H',sec,50,7)
        geom=extra_trigger(replace(geom,'SECTORS',bytes(sec)),0,88,7,0)
        samples=[self.state(geom,f'40:2,{tic-40}:0') for tic in range(136,150)]
        reversals=[s for s in samples if any(e['sound'].endswith('start') for e in s['moverSounds']) and s['floorMovers'][0]['status'].endswith('down')]
        self.assertEqual(len(reversals),1)
        result=reversals[0]
        self.assertEqual(result['floors'][1],48)
        self.assertEqual(result['feet'],48)
        self.assertEqual(result['health'],100)
        self.assertEqual(result['floorMovers'][0]['count'],105)
        self.assertTrue(any(s['floors'][1]<48 and s['floorMovers'][0]['status'].endswith('down') for s in samples))

    def test_partition_and_restart_preserve_mover_state(self):
        for special in (36,88):
            geom=mover_room(special)
            self.assertEqual(self.state(geom,'10:2,120:0'),self.state(geom,'5:2,5:2,30:0,90:0'))
            self.assertEqual(self.state(geom,'0:0'),self.state(geom,'10:2,60:0,1:1024'))

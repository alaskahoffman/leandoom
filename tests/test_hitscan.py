"""Original hitscan through live WAD/player/actor links and combat dispatch."""
import json
import struct
import subprocess
from pathlib import Path
import collision_reference
import fidelity_reference
import unittest
import test_assets
from test_assets import replace
from test_combat import arena
from test_render import two_rooms
from test_things import things,sectors
from test_wad import pack


def wall_scene(included=True,special=0):
    geom=arena([(160,0,0,3004,7)])
    vertices=dict(geom)['VERTEXES'];n=len(vertices)//4
    geom=replace(geom,'VERTEXES',vertices+pack('4h',64,128,64,-128))
    geom=replace(geom,'LINEDEFS',dict(geom)['LINEDEFS']+pack('7H',n,n+1,1,special,0,0,65535))
    ids=list(range(5 if included else 4))
    return replace(geom,'BLOCKMAP',pack('hhHH',-256,-256,4,4)+pack('16H',*([20]*16))+pack(f'{len(ids)+2}H',0,*ids,65535))


class HitscanTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        output=self.directory/'hitscan.json'
        self.run_cli(['combat','E1M1',script,output],geom)
        return json.loads(output.read_text())

    def test_bridge_corner_miss_matches_original_and_one_unit_step_recovers(self):
        # E1M1 thing 10: shooter (3008,-2848), zombieman (2912,-2816).
        # Crop empty BLOCKMAP cells while preserving the original grid alignment.
        # At this exact angle both original traces stall at the shared corner:
        # the center aim misses, a side retry finds a slope, but the bullet still
        # never visits the target cell. Keep this historical quirk, not an enlarged
        # hitbox or a special case for this enemy. One unit in any direction fixes it.
        unit=65536;angle=1927746431;commands=[]
        positions=[(3008,-2848),(3007,-2848),(3009,-2848),(3008,-2847),(3008,-2849)]
        for x,y in positions:
            commands += ['reset','grid 2552 -3336 8 8',
                f'line 0 0 0 {unit} {-24*unit} {176*unit} 0 0 0',
                f'thing {x*unit} {y*unit} {16*unit} 1',f'shootmeta 0 1 0 {-24*unit} {56*unit}',
                f'thing {2912*unit} {-2816*unit} {20*unit} 1',f'shootmeta 1 1 0 {-24*unit} {56*unit}',
                'link 27 0','link 34 1',f'aim 0 {angle} {1024*unit}',f'bulletslope 0 {angle}',
                f'shoot 0 {angle} {2048*unit} -4903 5']
        input=self.directory/'bridge.txt';input.write_text('\n'.join(commands)+'\n')
        root=Path(__file__).resolve().parents[1]
        actual=subprocess.check_output([str(root/'.lake/build/bin/collision-probe'),str(input)])
        # sources() checks the pinned upstream hashes. All routines are unchanged;
        # the existing bounded C host suffices for this reduced map case.
        source=self.directory/'bridge.c'
        source.write_text(collision_reference.oracle_source(fidelity_reference.sources()))
        for optimization in ['-O0','-O2']:
            exe=self.directory/('bridge'+optimization)
            subprocess.run(['cc','-std=c11',optimization,'-fwrapv',str(source),'-o',str(exe)],check=True,capture_output=True)
            expected=subprocess.check_output([str(exe),str(input)])
            self.assertEqual(actual,expected,optimization)
        shots=[row for command,row in zip(commands,actual.decode().splitlines()) if command.startswith('shoot ')]
        self.assertEqual(shots[0].split('|')[0].strip(),'')
        self.assertIn('| 128 ',shots[0]) # 64 repeated block visits, lines then things.
        for row in shots[1:]:self.assertIn('d 1 5 0 0',row.split('|')[0])

    def test_solid_nonshootable_decoration_does_not_absorb_bullet(self):
        result=self.state(arena([(160,0,0,3004,7)],extras=[(64,0,0,2028,7)]),'5:8192')
        self.assertEqual(result['actors'][0]['health'],5)
        self.assertEqual([e['kind'] for e in result['shotEvents']],['blood','damage'])

    def test_barrel_stops_bullet_with_puff_before_damage_request(self):
        result=self.state(arena([(160,0,0,3004,7)],extras=[(64,0,0,2035,7)]),'5:8192')
        self.assertEqual(result['actors'][0]['health'],20)
        self.assertEqual([e['kind'] for e in result['shotEvents']],['puff','damage'])
        self.assertEqual(result['shotEvents'][-1]['target'],2)
        self.assertEqual(result['actors'][1]['health'],5)

    def test_actor_diagonal_intersection_replaces_cylinder_entry(self):
        # Cylinder entry would hit (80,-12) first; after the BLOCKMAP boundary
        # nudge the original actor diagonals put (90,0) first instead.
        result=self.state(arena([(90,0,0,3004,7),(80,-12,0,3004,7)]),'5:8192')
        self.assertEqual([(a['x'],a['health']) for a in result['actors']],[(90,5),(80,20)])
        self.assertEqual(result['shotEvents'][-1]['target'],1)

    def test_blockmap_omission_is_respected(self):
        blocked=self.state(wall_scene(),'5:8192')
        self.assertEqual(blocked['actors'][0]['health'],20)
        self.assertEqual([e['kind'] for e in blocked['shotEvents']],['puff'])
        omitted=self.state(wall_scene(False),'5:8192')
        self.assertEqual(omitted['actors'][0]['health'],5)
        self.assertEqual(omitted['shotEvents'][-1]['kind'],'damage')

    def test_vertical_autoaim_uses_actor_height_through_portal(self):
        geom=things(sectors(two_rooms(),first=(0,128),second=(24,128)),[(0,0,0,1,7),(144,0,0,3004,7)])
        result=self.state(geom,'5:8192')
        self.assertEqual(result['actors'][0]['health'],5)
        self.assertGreater(result['shotSlope'],0)
        blood=next(e for e in result['shotEvents'] if e['kind']=='blood')
        self.assertGreater(blood['z'],36)
        self.assertLess(blood['z'],80)

    def test_shooting_exit_records_special_but_does_not_use_it(self):
        result=self.state(wall_scene(special=11),'5:8192')
        self.assertEqual([e['kind'] for e in result['shotEvents']],['special','puff'])
        self.assertEqual(result['specials'][-1],11)
        self.assertFalse(result['exitRequested'])

    def test_unported_shoot_special_reports_error(self):
        output=self.directory/'unsupported.json'
        result=self.run_cli(['combat','E1M1','5:8192',output],wall_scene(special=46),ok=False)
        self.assertIn('shoot-activated special 46 is not ported',result.stderr)

    def test_trace_reset_and_script_partition(self):
        geom=arena([(160,0,0,3004,7)])
        whole=self.state(geom,'19:8192')
        self.assertEqual(whole,self.state(geom,'5:8192,14:8192'))
        self.assertEqual(self.state(geom,'19:8192,1:1024'),self.state(geom,'0:0'))
        self.assertEqual(self.state(geom,'5:8192,1:0')['shotEvents'],[])

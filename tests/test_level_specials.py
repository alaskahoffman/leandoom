"""Exit requests and secrets through the runtime's actual WAD/player paths."""
import json
import struct
import unittest
import test_assets
from test_assets import replace
from test_render import two_rooms
from test_things import things,sectors
from test_wad import room,name


def secret_room(geom=None,indices=(0,)):
    geom=room() if geom is None else geom
    data=bytearray(dict(geom)['SECTORS'])
    for index in indices:struct.pack_into('<H',data,index*26+22,9)
    return replace(geom,'SECTORS',data)


def exit_room(top='-',middle='SW1EXIT',bottom='-',flags=1):
    geom=things(room(),[(0,16,90,1,7)])
    lines=bytearray(dict(geom)['LINEDEFS'])
    struct.pack_into('<HH',lines,14+4,flags,11)
    sides=bytearray(dict(geom)['SIDEDEFS'])
    sides[4:12]=name(top);sides[12:20]=name(bottom);sides[20:28]=name(middle)
    return replace(replace(geom,'LINEDEFS',lines),'SIDEDEFS',sides)


class LevelSpecialTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script,patches=()):
        output=self.directory/'level.json'
        self.run_cli(['simulate','E1M1',script,output],geom,patches)
        return json.loads(output.read_text())

    def test_secret_total_discovery_once_and_restart(self):
        geom=secret_room(two_rooms(),(0,1))
        initial=self.state(geom,'0:0')
        self.assertEqual((initial['secrets'],initial['totalSecrets']),(0,2))
        found=self.state(geom,'1:0')
        self.assertEqual(found['sectorSpecials'],[0,9])
        self.assertEqual((found['secrets'],found['totalSecrets']),(1,2))
        self.assertEqual(self.state(geom,'70:0')['secrets'],1)
        self.assertEqual(self.state(geom,'1:0,1:1024'),initial)

    def test_secret_uses_pre_movement_sector(self):
        geom=secret_room(things(sectors(two_rooms(),first=(0,128),second=(0,128)),[(48,0,0,1,7)]),(1,))
        entered=self.state(geom,'7:2')
        self.assertGreater(entered['x'],64)
        self.assertEqual(entered['secrets'],0)
        discovered=self.state(geom,'8:2')
        self.assertEqual(discovered['secrets'],1)
        self.assertEqual(discovered['sectorSpecials'][1],0)

    def test_lower_sector_waits_for_landing_not_collision_floor(self):
        geom=secret_room(things(sectors(two_rooms(),first=(0,128),second=(-32,128)),[(48,0,0,1,7)]),(1,))
        samples=[self.state(geom,f'{tic}:2') for tic in range(7,30)]
        self.assertEqual(samples[0]['feet'],0)
        self.assertEqual(samples[0]['secrets'],0)
        landing=next(i for i,s in enumerate(samples) if s['feet']==-32)
        self.assertEqual(samples[landing]['secrets'],0)
        self.assertEqual(samples[landing+1]['secrets'],1)

    def test_secret_partition_and_two_discoveries(self):
        geom=secret_room(sectors(two_rooms(),first=(0,128),second=(0,128)),(0,1))
        whole=self.state(geom,'35:2')
        self.assertEqual(whole['secrets'],2)
        self.assertEqual(whole,self.state(geom,'10:2,25:2'))

    def test_exit_flips_clears_requests_and_holds_at_completion_boundary(self):
        geom=exit_room(flags=33)
        # Scrollers still run on the exit activation tic; no further gameplay
        # tics run while the unported completion/intermission stage is pending.
        lines=bytearray(dict(geom)['LINEDEFS']);struct.pack_into('<H',lines,6,48)
        geom=replace(geom,'LINEDEFS',lines)
        initial=self.state(geom,'0:0')
        exited=self.state(geom,'1:4096')
        self.assertTrue(exited['exitRequested'])
        self.assertFalse(exited['secretExit'])
        self.assertEqual(exited['specials'][1],0)
        self.assertEqual(exited['textures'][0],['-','SW2EXIT','-'])
        self.assertEqual(exited['exitSwitchSound'],'swtchn')
        self.assertEqual(exited['sideOffsets'][0],initial['sideOffsets'][0]+1)
        self.assertEqual(self.state(geom,'35:4096'),exited)
        self.assertEqual(self.state(geom,'1:4096,20:2'),exited)
        self.assertEqual(self.state(geom,'1:4096,1:1024'),initial)

    def test_exit_unknown_texture_still_completes_without_sound(self):
        result=self.state(exit_room(middle='SW1FAKE'),'1:4096')
        self.assertTrue(result['exitRequested'])
        self.assertEqual(result['textures'][0][1],'SW1FAKE')
        self.assertEqual(result['exitSwitchSound'],'')

    def test_exit_switch_table_order_precedes_slot_order_and_reverses(self):
        result=self.state(exit_room(top='SW1EXIT',bottom='SW1BRCOM'),'1:4096')
        self.assertEqual(result['textures'][0],['SW1EXIT','SW1EXIT','SW2BRCOM'])
        result=self.state(exit_room(middle='SW2EXIT'),'1:4096')
        self.assertEqual(result['textures'][0][1],'SW1EXIT')

    def test_exit_rejects_back_side_and_out_of_reach(self):
        geom=things(two_rooms(),[(80,0,180,1,7)])
        lines=bytearray(dict(geom)['LINEDEFS']);struct.pack_into('<H',lines,2*14+6,11)
        result=self.state(replace(geom,'LINEDEFS',lines),'1:4096')
        self.assertFalse(result['exitRequested'])
        self.assertEqual(result['specials'][2],11)
        far=things(exit_room(),[(0,-16,90,1,7)])
        self.assertFalse(self.state(far,'1:4096')['exitRequested'])

    def test_switch_mode_comes_from_base_archive(self):
        geom=exit_room(middle='SW1BLUE')
        self.assertEqual(self.state(geom,'1:4096')['textures'][0][1],'SW1BLUE')
        self.assertEqual(self.state(geom+[('E2M1',b'')],'1:4096')['textures'][0][1],'SW2BLUE')
        self.assertEqual(self.state(geom,'1:4096',([('E2M1',b'')],))['textures'][0][1],'SW1BLUE')

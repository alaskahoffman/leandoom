"""Shootable imps and original barrel death/blast integration in the viewer path."""
import json
import subprocess
import unittest
from pathlib import Path
import test_assets
from test_assets import patch,replace
from test_combat import arena,combat_art
from test_render import two_rooms
from test_things import things,sectors
from test_wad import wad

ROOT=Path(__file__).resolve().parents[1]


class BarrelImpTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        output=self.directory/'state.json'
        self.run_cli(['combat','E1M1',script,output],geom)
        return json.loads(output.read_text())

    def killed(self,geom,script,health=0,target=1):
        path=self.directory/'killed.wad';path.write_bytes(wad(geom))
        output=self.directory/'killed.json'
        subprocess.run([str(ROOT/'.lake/build/bin/death-probe'),'runtime',str(path),str(target),str(health),script,str(output)],check=True,capture_output=True,timeout=15)
        return json.loads(output.read_text())

    def test_imp_takes_pistol_damage_pain_and_dies(self):
        geom=arena([(96,0,0,3001,7)])
        first=self.state(geom,'5:8192')['actors'][0]
        self.assertEqual((first['health'],first['pose']),(50,'TROOE'))
        self.assertEqual(self.state(geom,'33:8192')['actors'][0]['pose'],'TROOH')
        dead=self.state(geom,'100:8192,40:0')
        self.assertEqual(dead['kills'],1)
        self.assertEqual(dead['actors'][0]['pose'],'TROOM')
        self.assertFalse(dead['actors'][0]['death']['solid'])
        self.assertEqual(dead['dropped'],[])

    def test_imp_extreme_threshold_and_late_fall(self):
        geom=arena([(96,0,0,3001,7)])
        self.assertEqual(self.killed(geom,'0:0',-60)['actors'][0]['pose'],'TROOI')
        self.assertEqual(self.killed(geom,'0:0',-61)['actors'][0]['pose'],'TROON')
        self.assertTrue(self.killed(geom,'14:0',-61)['actors'][0]['death']['solid'])
        self.assertFalse(self.killed(geom,'15:0',-61)['actors'][0]['death']['solid'])

    def test_barrel_pistol_damage_has_no_pain_chase_or_kill_credit(self):
        geom=arena([(96,0,0,2035,7)])
        first=self.state(geom,'5:8192')
        self.assertEqual(first['actors'][0]['health'],5)
        self.assertTrue(first['actors'][0]['mode'].endswith('idle'))
        self.assertEqual(first['actors'][0]['damageTarget'],-1)
        self.assertEqual(first['actors'][0]['x'],96)
        self.assertEqual([e['kind'] for e in first['shotEvents']],['puff','damage'])
        dead=self.state(geom,'20:8192')
        self.assertEqual(dead['actors'][0]['health'],0)
        self.assertEqual(dead['kills'],0)
        self.assertEqual(dead['dropped'],[])

    def test_blast_is_delayed_until_bexp4_then_barrel_is_removed(self):
        geom=arena([(96,0,0,2035,7)])
        before=self.killed(geom,'14:0')
        blast=self.killed(geom,'15:0')
        self.assertEqual(before['health'],100)
        self.assertEqual(before['actors'][0]['pose'],'BEXPC')
        self.assertEqual(blast['health'],52)  # 128 - (96 - player radius 16).
        self.assertEqual(blast['actors'][0]['pose'],'BEXPD')
        self.assertEqual(blast['actors'][0]['death']['height'],10.5)
        self.assertTrue(blast['actors'][0]['death']['solid'])
        self.assertEqual(blast['blastEvents'],[{'spot':1,'target':-1,'damage':48}])
        self.assertFalse(self.killed(geom,'34:0')['actors'][0]['removed'])
        removed=self.killed(geom,'35:0')
        self.assertTrue(removed['actors'][0]['removed'])
        self.assertEqual(self.killed(geom,'100:0')['health'],52)

    def test_barrel_chain_is_delayed_and_damages_imps(self):
        geom=arena([(48,0,0,2035,7),(96,0,0,2035,7),(144,0,0,3001,7)])
        first=self.killed(geom,'15:0')
        self.assertEqual([a['health'] for a in first['actors']],[0,0,8])
        self.assertTrue(first['actors'][1]['pose'].startswith('BEXP'))
        end=self.killed(geom,'80:0')
        self.assertEqual(end['actors'][2]['health'],0)
        self.assertEqual(end['kills'],1)
        self.assertTrue(all(a['removed'] for a in end['actors'][:2]))

    def test_closed_portal_and_reject_block_blast(self):
        for blocked in [False,True]:
            geom=things(sectors(two_rooms(),first=(-16,128),second=(-16,-16 if blocked else 128)),[(0,0,0,1,7),(0,0,0,2035,7),(144,0,0,3001,7)])
            state=self.killed(geom,'15:0')
            self.assertEqual(state['actors'][1]['health'],60 if blocked else 56)
        rejected=replace(geom,'REJECT',bytes([0xff]))
        self.assertEqual(self.killed(rejected,'15:0')['health'],100)

    def test_barrel_without_remembered_attacker_causes_environment_death(self):
        geom=arena([(0,0,0,2035,7)])
        dead=self.killed(geom,'15:0')
        self.assertEqual(dead['health'],0)
        self.assertEqual(dead['frags'],[1,0,0,0])

    def test_surviving_hit_sets_barrel_source_but_lethal_hit_does_not(self):
        geom=arena([(96,0,0,2035,7)])
        self.assertEqual(self.state(geom,'20:8192')['actors'][0]['damageTarget'],-1)
        self.assertIsNone(self.killed(geom,'0:0')['actors'][0]['damageTarget'])

    def test_reset_and_partition_restore_barrels_and_imps(self):
        geom=arena([(48,0,0,2035,7),(96,0,0,2035,7),(144,0,0,3001,7)])
        self.assertEqual(self.killed(geom,'80:0'),self.killed(geom,'14:0,1:0,65:0'))
        self.assertEqual(self.killed(geom,'80:0,1:1024'),self.state(geom,'0:0'))

    def test_viewer_assets_include_explosion_and_extreme_imp_frames(self):
        geom=arena([(96,0,0,2035,7),(160,0,0,3001,7)])+combat_art()
        geom += [(f'TROO{chr(65+i)}0',patch([[100+i]*8 for _ in range(56)],4,56)) for i in range(21)]
        geom += [(f'BAL1{c}0',patch([[245]*8 for _ in range(8)],4,4)) for c in 'ABCDE']
        geom += [(f'BAR1{c}0',patch([[150]*8 for _ in range(42)],4,42)) for c in 'AB']
        geom += [(f'BEXP{c}0',patch([[151+i]*32 for _ in range(48)],16,48)) for i,c in enumerate('ABCDE')]
        output=self.directory/'frame.ppm'
        self.run_cli(['render-combat','E1M1','35:8192',output],geom)
        self.assertTrue(output.read_bytes().startswith(b'P6'))
        for missing in ['BEXPD0','TROOU0']:
            failure=self.run_cli(['render-combat','E1M1','0:0',output],[(n,b) for n,b in geom if n!=missing],ok=False)
            self.assertIn(missing[:5],failure.stderr)


if __name__=='__main__':unittest.main()

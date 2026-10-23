"""Connect the original C door states to real WAD use actions and simulation."""
import json
import unittest
import test_assets
from test_simulation import door_room, switch_room
import doors_reference
import fidelity_reference


class DoorKernelTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        path=self.directory/'door.json'
        self.run_cli(['simulate','E1M1',script,path],geom)
        return json.loads(path.read_text())

    def test_wad_door_tics_match_original_c(self):
        golden=fidelity_reference.checked_golden()['groups']['door_runtime']['expected']
        cursor=0
        for case in doors_reference.runtime_cases():
            special,_,ceiling,_,_=case
            geom=door_room(special) if special in (1,31,118) else switch_room(special,open_door=ceiling==124)
            for tic in (0,1,17,18,69,70,71,150,220,221,222,291,292,299):
                with self.subTest(special=special,tic=tic):
                    # The activation tic already executes the new thinker.
                    fields,events=golden[cursor+tic+1].split(' /')
                    _,_,floor,ceiling,speed,top,direction,wait,count,removed,busy=fields.split()
                    result=self.state(geom,f'1:4096,{tic}:0')
                    self.assertEqual(result['ceilings'][1]*65536,int(ceiling))
                    expected=[] if int(removed) else [{'sector':1,'direction':int(direction),'wait':int(count)}]
                    self.assertEqual(result['doors'],expected)
                    sounds=events.split(' s ')[1:]
                    expected_sounds=[('close','open','blazeClose')[int(s)] for s in sounds]
                    self.assertEqual([s['sound'].split('.')[-1] for s in result['doorSounds']],expected_sounds)
            cursor+=len(doors_reference.runtime_commands(case))
        self.assertEqual(cursor,len(golden))

    def test_fast_door_reversal_requests_ordinary_open_sound(self):
        geom=switch_room(111,extras=[(110,0,0,3004,7)])
        result=self.state(geom,'1:4096,178:0')
        self.assertEqual(result['ceilings'][1],44)
        self.assertEqual(result['doors'][0]['direction'],1)
        self.assertEqual([s['sound'].split('.')[-1] for s in result['doorSounds']],['open'])

    def test_close_only_obstruction_rolls_back_without_reversing(self):
        for special in (50,113):
            result=self.state(switch_room(special,open_door=True,extras=[(110,0,0,3004,7)]),'1:4096,100:0')
            self.assertGreaterEqual(result['ceilings'][1],40)
            self.assertEqual(result['doors'][0]['direction'],-1)
            self.assertEqual(result['doorSounds'],[])

    def test_door_boundary_state_survives_script_partition_and_restart(self):
        geom=door_room()
        self.assertEqual(self.state(geom,'72:4096'),self.state(geom,'71:4096,1:4096'))
        self.assertEqual(self.state(geom,'0:0'),self.state(geom,'223:4096,1:1024'))

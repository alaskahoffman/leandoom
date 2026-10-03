"""The runtime WAD/key adapter must reach the pinned C movement states."""
import json
import unittest
import test_assets
import fidelity_reference as reference
import world_reference
from test_wad import room, pack
from test_things import things


class WalkingTests(unittest.TestCase):
    setUp = test_assets.AssetTests.setUp
    tearDown = test_assets.AssetTests.tearDown
    run_cli = test_assets.AssetTests.run_cli

    def test_wad_and_keyboard_bridge_matches_c(self):
        expected=reference.checked_golden()['groups']['walking_bridge']['expected']
        cursor=0
        for (label,x,y,segments),commands in zip(world_reference.walking_cases(),world_reference.walking_commands()):
            cursor+=len(commands)
            fields=expected[cursor-1].split(' | ')
            actor=list(map(int,fields[0].split()))[1:8]
            physics=list(map(int,fields[3].split()))
            with self.subTest(case=label):
                output=self.directory/'state.json'
                script=','.join(f'{ticks}:{mask}' for ticks,mask,_ in segments)
                self.run_cli(['simulate','E1M1',script,output],things(room(),[(x,y,0,1,7)]))
                state=json.loads(output.read_text())
                raw=lambda v: round(v*65536)
                self.assertEqual([raw(state[k]) for k in ('x','y','feet')],actor[:3])
                self.assertEqual([raw(v) for v in state['momentum']],physics[:3])
                self.assertEqual(state['angle'],physics[3])
                self.assertEqual(raw(state['viewHeight']),physics[5])
                self.assertEqual(raw(state['eye']),physics[7])

    def test_runtime_rejects_unsupported_blockmap(self):
        payload=pack('hhHHH',-128,-128,1,1,32768)
        payload+=bytes(32768*2-len(payload))+pack('6H',0,0,1,2,3,65535)
        lumps=[(name,payload if name=='BLOCKMAP' else data) for name,data in room()]
        result=self.run_cli(['walk','E1M1',1,2],lumps,ok=False)
        self.assertIn('outside the vanilla profile',result.stderr)

"""Original trace evidence must fail closed, independently of engine parity."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import original_demo_compare as oc

COMMANDS = [[17,-9,-768,0]]*50


def records():
    return [{'tick':i,'command':COMMANDS[i-1] if i else None,
             'state':{'levelTime':i,'rng':{'play':144,'misc':0},
                      'player':{**dict.fromkeys(oc.PLAYER_SCALARS,0),'ammo':[0,0,0,0],'pendingWeapon':None},
                      'weapon':dict.fromkeys(oc.dc.WEAPON_FIELDS,0),'projectiles':[],'exitRequested':False,
                      'enemyBrains':{str(e['id']):dict.fromkeys(oc.dc.BRAIN_FIELDS,0) for e in oc.SPEC['enemy_profile']}}} for i in range(51)]


class OriginalTraceTests(unittest.TestCase):
    def test_exit_request_is_required_boolean_and_compared(self):
        changed=records();changed[-1]['state']['exitRequested']=True
        difference=oc.compare(records(),changed,COMMANDS,'exit-mutated')['first_divergence']
        self.assertEqual((difference['tick'],difference['differences'][0]['field']),
                         (50,'state.exitRequested'))
        for value in [0,1,None,'false']:
            changed=records();changed[-1]['state']['exitRequested']=value
            with self.assertRaises(ValueError):oc.validate_records(changed,COMMANDS)
        changed=records();changed[0]['state'].pop('exitRequested')
        with self.assertRaises(ValueError):oc.validate_records(changed,COMMANDS)
        changed=records();changed[42]['state']['exitRequested']=True
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'trace.jsonl'
            path.write_text(''.join(json.dumps(r)+'\n' for r in changed))
            with self.assertRaisesRegex(ValueError,'intermission'):oc.read_records(path,COMMANDS)

    def test_projectile_fields_order_removal_and_schema(self):
        shot={**dict.fromkeys(oc.dc.PROJECTILE_FIELDS,0),'state':97,'source':9,'missile':1}
        baseline=records();baseline[42]['state']['projectiles']=[shot,{**shot,'source':17}]
        for field in oc.dc.PROJECTILE_FIELDS:
            changed=copy.deepcopy(baseline);changed[42]['state']['projectiles'][0][field]^=1
            # Source identities are semantic IDs, not arbitrary bit patterns.
            if field=='source':changed[42]['state']['projectiles'][0][field]=17
            if field=='state':changed[42]['state']['projectiles'][0][field]=98
            result=oc.compare(baseline,changed,COMMANDS,'mutated')['first_divergence']
            self.assertEqual((result['tick'],result['differences'][0]['field']),
                             (42,f'state.projectiles[0].{field}'))
            changed[42]['state']['projectiles'][0].pop(field)
            with self.assertRaises(ValueError):oc.validate_records(changed,COMMANDS)
        changed=copy.deepcopy(baseline);changed[42]['state']['projectiles'].reverse()
        self.assertEqual(oc.compare(baseline,changed,COMMANDS,'reordered')['first_divergence']['tick'],42)
        changed=copy.deepcopy(baseline);changed[42]['state']['projectiles'].pop()
        self.assertEqual(oc.compare(baseline,changed,COMMANDS,'removed')['first_divergence']['differences'][0]['field'],
                         'state.projectiles.length')
        for field,value in [('angle',-1),('x',True),('source',1000),('lastlook',4),('missile',2),('state',102)]:
            changed=copy.deepcopy(baseline);changed[42]['state']['projectiles'][0][field]=value
            with self.assertRaises(ValueError):oc.validate_records(changed,COMMANDS)
        changed=records();changed[0]['state'].pop('projectiles')
        with self.assertRaises(ValueError):oc.validate_records(changed,COMMANDS)

    def test_match_is_limited_to_declared_fields(self):
        r=oc.compare(records(),records(),COMMANDS,'lean')
        self.assertEqual(r['status'],'match')
        self.assertEqual(r['ticks_compared'],50)
        self.assertIsNone(r['first_divergence'])
        self.assertEqual(len(oc.SPEC['compared']),21)
        self.assertEqual(oc.SPEC['schema'],'leandoom-original-tic-trace-v6')

    def test_player_and_weapon_fields_are_required_and_compared(self):
        for group,fields in [('player',['health','armor','armorType','readyWeapon','secrets']),
                             ('weapon',oc.dc.WEAPON_FIELDS)]:
            for field in fields:
                with self.subTest(group=group,field=field):
                    changed=records(); changed[42]['state'][group][field]^=1
                    r=oc.compare(records(),changed,COMMANDS,'lean')['first_divergence']
                    self.assertEqual((r['tick'],r['differences']),
                        (42,[{'field':f'state.{group}.{field}','original':0,'candidate':1}]))
                    changed[42]['state'][group].pop(field)
                    with self.assertRaises(ValueError): oc.validate_records(changed,COMMANDS)
        for index in range(4):
            changed=records(); changed[42]['state']['player']['ammo'][index]=1
            r=oc.compare(records(),changed,COMMANDS,'lean')['first_divergence']
            self.assertEqual(r['tick'],42)
            self.assertEqual(r['differences'][0]['field'],f'state.player.ammo[{index}]')
        changed=records();changed[42]['state']['player']['pendingWeapon']=2
        r=oc.compare(records(),changed,COMMANDS,'lean')['first_divergence']
        self.assertEqual(r['differences'],[{'field':'state.player.pendingWeapon','original':None,'candidate':2}])

    def test_rejects_old_partial_schema_and_malformed_weapon_inventory(self):
        for change in [lambda s:s.pop('weapon'),lambda s:s['player'].pop('ammo'),
                       lambda s:s['player'].pop('pendingWeapon'),lambda s:s['player'].update(ammo=[0]*3),
                       lambda s:s['player'].update(ammo=[0,0,True,0]),
                       lambda s:s['player'].update(ammo=[0,0,0,2**31]),
                       lambda s:s['player'].update(pendingWeapon=9),
                       lambda s:s['player'].update(pendingWeapon=False),
                       lambda s:s['player'].update(readyWeapon=9),
                       lambda s:s['weapon'].update(state=967),
                       lambda s:s['weapon'].update(flashState=-1),
                       lambda s:s['weapon'].update(tics=2**31),
                       lambda s:s['weapon'].update(x=True)]:
            rows=records();change(rows[0]['state'])
            with self.assertRaises(ValueError):oc.validate_records(rows,COMMANDS)

    def test_projection_preserves_observations_and_never_fills_missing_fields(self):
        from test_demo_compare import state
        rows=records();diagnostic=[]
        for row in rows:
            s=state();s['levelTime']=row['tick'];s['enemyBrains']=row['state']['enemyBrains']
            s['player'].update(row['state']['player']);s['weapon']=row['state']['weapon'];s['rng']=row['state']['rng']
            diagnostic.append({**row,'state':s})
        self.assertEqual(oc.project(diagnostic,COMMANDS),rows)
        for group,field in [('player','health'),('player','ammo'),('player','pendingWeapon'),('weapon','flashTics')]:
            broken=copy.deepcopy(diagnostic);broken[42]['state'][group].pop(field)
            with self.assertRaises(ValueError):oc.project(broken,COMMANDS)

    def test_detects_exact_single_bit_position_boundary(self):
        changed=records(); changed[42]['state']['player']['x']^=1
        r=oc.compare(records(),changed,COMMANDS,'lean')
        self.assertEqual(r['first_divergence']['tick'],42)
        self.assertEqual(r['first_divergence']['differences'],
                         [{'field':'state.player.x','original':0,'candidate':1}])

    def test_enemy_motion_and_health_are_observed_and_required(self):
        for field in ['x','y','z','momx','momy','momz','health']:
            changed=records();changed[42]['state']['enemyBrains']['87'][field]^=1
            r=oc.compare(records(),changed,COMMANDS,'lean')
            self.assertEqual(r['first_divergence']['tick'],42)
            self.assertEqual(r['first_divergence']['differences'],
                [{'field':f'state.enemyBrains.87.{field}','original':0,'candidate':1}])
            changed[42]['state']['enemyBrains']['87'].pop(field)
            with self.assertRaises(ValueError):oc.validate_records(changed,COMMANDS)

    def test_initialization_mismatch_and_later_field_are_both_reported(self):
        changed=records(); changed[0]['state']['rng']['play']=5
        changed[49]['state']['player']['momx']=-1
        r=oc.compare(records(),changed,COMMANDS,'lean')
        self.assertEqual(r['first_divergence']['phase'],'initialization')
        self.assertEqual(r['first_by_field']['state.player.momx']['tick'],49)

    def test_candidate_leveltime_difference_is_behavioral(self):
        changed=records(); changed[10]['state']['levelTime']=9
        r=oc.compare(records(),changed,COMMANDS,'lean')
        self.assertEqual(r['first_divergence']['tick'],10)
        self.assertEqual(r['first_divergence']['differences'][0]['field'],'state.levelTime')

    def test_input_mismatch_invalidates_even_an_earlier_divergence(self):
        changed=records(); changed[0]['state']['rng']['play']=5
        changed[-1]['command']=[0,0,0,0]
        with self.assertRaisesRegex(ValueError,'input/boundary mismatch'):
            oc.compare(records(),changed,COMMANDS,'lean')

    def test_rejects_missing_extra_and_noncontiguous_records(self):
        for rows in [records()[:-1],records()+[records()[-1]],records()[1:]]:
            with self.subTest(length=len(rows)), self.assertRaises(ValueError):
                oc.validate_records(rows,COMMANDS)
        rows=records(); rows[10]['tick']=9
        with self.assertRaises(ValueError): oc.validate_records(rows,COMMANDS)
        with self.assertRaises(ValueError): oc.validate_records([records()[0]],[])

    def test_rejects_bad_types_unknown_fields_and_out_of_range_values(self):
        mutations=[lambda r:r['state']['rng'].update(play=True),
                   lambda r:r['state']['rng'].update(play=256),
                   lambda r:r['state']['player'].update(x=2**31),
                   lambda r:r['state']['player'].update(angle=-1),
                   lambda r:r['state']['player'].update(ammo=50),
                   lambda r:r.update(tick=False),
                   lambda r:r.update(command=[0,0,0,0]),
                   lambda r:r['state'].pop('rng'),
                   lambda r:r['state']['enemyBrains'].pop('87'),
                   lambda r:r['state']['enemyBrains']['87'].update(target=999),
                   lambda r:r['state']['enemyBrains']['87'].update(state=967),
                   lambda r:r['state']['enemyBrains']['87'].update(behaviorFlags=1)]
        for mutation in mutations:
            rows=records(); mutation(rows[0])
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                oc.validate_records(rows,COMMANDS)

    def test_original_boundary_leveltime_must_agree_with_observer_count(self):
        rows=records(); rows[12]['state']['levelTime']=11
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'trace.jsonl'
            path.write_text(''.join(json.dumps(r)+'\n' for r in rows))
            with self.assertRaisesRegex(ValueError,'original level time mismatch'):
                oc.read_records(path,COMMANDS)


@unittest.skipUnless((ROOT/'artifacts/doom-shareware-1.9/doom19s.zip').exists(),
                     'original shareware archive not installed')
class OriginalImageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.binary=oc.original_image()

    def test_pinned_image_instruction_and_relocation_evidence(self):
        self.assertEqual(len(oc.verify_image(self.binary)),709905)

    def test_any_executable_mutation_is_rejected(self):
        binary=bytearray(self.binary); binary[0x42014+0x2081a]^=1
        with self.assertRaisesRegex(ValueError,'SHA-256 mismatch'): oc.verify_image(binary)

    def test_wrong_data_binding_profile_is_rejected(self):
        spec=copy.deepcopy(oc.SPEC); spec['data_operands']['0x32fad']='0x2ae7c'
        with patch.object(oc,'SPEC',spec),self.assertRaisesRegex(ValueError,'relocation mismatch'):
            oc.verify_image(self.binary)

    def test_wrong_enemy_offset_is_rejected(self):
        spec=copy.deepcopy(oc.SPEC); spec['enemy_offsets']['tics']=100
        with patch.object(oc,'SPEC',spec),self.assertRaisesRegex(ValueError,'enemy field offset mismatch'):
            oc.verify_image(self.binary)

    def test_wrong_player_psprite_offsets_and_layout_are_rejected(self):
        for group in ['player','psprite','projectile']:
            for field in oc.SPEC[group+'_offsets']:
                spec=copy.deepcopy(oc.SPEC);spec[group+'_offsets'][field]+=4
                with self.subTest(group=group,field=field),patch.object(oc,'SPEC',spec),self.assertRaisesRegex(ValueError,'field offset mismatch'):
                    oc.verify_image(self.binary)
        for field in oc.SPEC['player_layout']:
            spec=copy.deepcopy(oc.SPEC);spec['player_layout'][field]+=1
            with self.subTest(field=field),patch.object(oc,'SPEC',spec),self.assertRaisesRegex(ValueError,'unsupported player layout'):
                oc.verify_image(self.binary)

    def test_wrong_boundary_profile_is_rejected(self):
        spec=copy.deepcopy(oc.SPEC); spec['signature_hex']='00'*22
        with patch.object(oc,'SPEC',spec),self.assertRaisesRegex(ValueError,'unique expected'):
            oc.verify_image(self.binary)


if __name__=='__main__': unittest.main()

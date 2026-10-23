"""Comparison failures must distinguish engine divergence from invalid evidence."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_combat import arena
from test_wad import wad

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('demo_compare',ROOT/'scripts/demo_compare.py')
dc=importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)


def state():
    return dict(levelTime=0,exitRequested=False,rng=dict(play=0,misc=0),
                player={**dict.fromkeys(dc.PLAYER_FIELDS,0),'ammo':[50,0,0,0],'pendingWeapon':None},
                weapon=dict.fromkeys(dc.WEAPON_FIELDS,0),
                sectors=[dict(floor=0,ceiling=8388608,light=160,special=0)],
                lineSpecials=[0],sideOffsets=[0],actors={},impacts=[],enemyBrains={},projectiles=[])


def records():
    return [dict(tick=0,command=None,state=state()),dict(tick=1,command=[17,-9,-768,0],state=state())]


class DemoEncodingTests(unittest.TestCase):
    def test_exit_route_retains_secret_route_and_pinned_input_bytes(self):
        commands=dc.scenario('e1m1-exit')
        self.assertEqual(len(commands),2445)
        self.assertEqual(commands[:1961],dc.scenario('shotgun-secret'))
        data=dc.encode_demo(commands)
        self.assertEqual(dc.decode_demo(data),commands)
        self.assertEqual(dc.sha(data),'cd6c966592da1d23d35be0e54ec3ed92652aebee8e02d05131d02afdf4e42c52')
        self.assertEqual(commands[-1],[0,0,0,2])

    def test_shotgun_secret_route_retains_complete_encounter_and_input_bytes(self):
        commands=dc.scenario('shotgun-secret')
        self.assertEqual(len(commands),1961)
        self.assertEqual(commands[:521],dc.scenario('enemy-encounter'))
        data=dc.encode_demo(commands)
        self.assertEqual(dc.decode_demo(data),commands)
        self.assertEqual(dc.sha(data),'10c14af0dca28e097573c436f6f4edd509ad025cd235d9fef47ab537fb831f25')

    def test_signed_commands_and_vanilla_turn_quantization(self):
        commands=[[-127,-128,-32768,0],[127,127,32512,1],[17,-9,-768,20]]
        self.assertEqual(dc.decode_demo(dc.encode_demo(commands)),commands)

    def test_end_marker_only_at_command_boundary(self):
        # 0x80 as sidemove or angle is data, not DEMOMARKER.
        self.assertEqual(dc.decode_demo(dc.HEADER+bytes([0,128,128,0,128])),[[0,-128,-32768,0]])

    def test_rejects_truncation_missing_marker_and_trailing_payload(self):
        valid=dc.encode_demo([[0,0,0,0]])
        for data in [b'',valid[:12],valid[:15],valid[:-1],valid+b'x',dc.HEADER+b'\x80']:
            with self.subTest(data=data),self.assertRaises(ValueError): dc.decode_demo(data)

    def test_rejects_unsupported_header_fields(self):
        valid=dc.encode_demo([[0,0,0,0]])
        for offset in range(13):
            data=bytearray(valid); data[offset]=(data[offset]+1)%256
            with self.subTest(offset=offset),self.assertRaises(ValueError): dc.decode_demo(data)

    def test_rejects_special_buttons_and_unimplemented_weapon_selection(self):
        for button in [0x80,0x40,4|(3<<3),4|(7<<3)]:
            with self.subTest(button=button),self.assertRaises(ValueError):
                dc.decode_demo(dc.HEADER+bytes([0,0,0,button,128]))

    def test_never_silently_rounds_turns(self):
        with self.assertRaises(ValueError): dc.encode_demo([[0,0,1,0]])


class TraceComparisonTests(unittest.TestCase):
    def read(self, data):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'trace.jsonl'
            path.write_text(''.join(json.dumps(row)+'\n' for row in data))
            return dc.read_records(path)

    def test_matching_trace_is_explicitly_limited_to_declared_fields(self):
        rows=self.read(records()); report=dc.compare(rows,copy.deepcopy(rows))
        self.assertEqual(report['status'],'match')
        self.assertEqual(report['ticks_compared'],1)
        self.assertFalse(report['provenance_verified'])
        self.assertIn('framebuffer',report['excluded'])

    def test_initialization_is_compared(self):
        ref=records(); lean=copy.deepcopy(ref); lean[0]['state']['rng']['play']=1
        result=dc.compare(ref,lean)['first_divergence']
        self.assertEqual((result['tick'],result['phase']),(0,'initialization'))
        self.assertEqual(result['differences'][0]['field'],'state.rng.play')

    def test_one_bit_difference_reports_exact_tic_input_and_field(self):
        ref=records(); lean=copy.deepcopy(ref); lean[1]['state']['player']['x']=1
        result=dc.compare(ref,lean)['first_divergence']
        self.assertEqual(result['tick'],1)
        self.assertEqual(result['command'],[17,-9,-768,0])
        self.assertEqual(result['differences'],[dict(field='state.player.x',reference=0,lean=1)])
        self.assertEqual(result['previous_matching_tick'],0)

    def test_input_mismatch_cannot_hide_behind_initialization_divergence(self):
        ref=records(); lean=copy.deepcopy(ref)
        lean[0]['state']['rng']['play']=3; lean[1]['command'][0]=18
        with self.assertRaisesRegex(ValueError,'input/boundary'): dc.compare(ref,lean)

    def test_rejects_incomplete_or_reordered_traces(self):
        rows=records()
        with self.assertRaisesRegex(ValueError,'incomplete'): dc.compare(rows,rows[:1])
        for data in [[],rows[:1],rows[::-1],[rows[0],rows[0]]]:
            with self.subTest(data=data),self.assertRaises(ValueError): self.read(data)

    def test_missing_fields_and_float_substitutes_are_errors(self):
        for edit in [lambda s:s.pop('rng'),lambda s:s['player'].pop('x'),
                     lambda s:s['player'].update(x=0.0),lambda s:s.update(player={}),
                     lambda s:s['rng'].update(play=True)]:
            rows=records(); edit(rows[0]['state'])
            with self.assertRaises(ValueError): self.read(rows)

    def test_effect_coordinates_and_lifetimes_are_strictly_compared(self):
        ref=records()
        ref[1]['state']['impacts']=[dict.fromkeys(dc.IMPACT_FIELDS,0)]
        lean=copy.deepcopy(ref); lean[1]['state']['impacts'][0]['x']=1
        difference=dc.compare(self.read(ref),self.read(lean))['first_divergence']
        self.assertEqual(difference['differences'],[dict(field='state.impacts[0].x',reference=0,lean=1)])
        for bad in [None,[{}],[dict.fromkeys(dc.IMPACT_FIELDS,0.0)]]:
            broken=copy.deepcopy(ref); broken[1]['state']['impacts']=bad
            with self.assertRaises(ValueError): self.read(broken)

    def test_removed_actor_and_array_length_report_structural_differences(self):
        ref=records(); lean=copy.deepcopy(ref)
        ref[1]['state']['actors']['7']=dict(kind=3004,x=0,y=0,z=0,health=20)
        lean[1]['state']['sideOffsets'].append(0)
        d=dc.compare(ref,lean)['first_divergence']['differences']
        self.assertEqual({v['field'] for v in d},{'state.actors.7','state.sideOffsets.length'})


class LeanTraceTests(unittest.TestCase):
    def trace(self,commands,geometry=None,ok=True):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder); w=root/'fixture.wad'; f=root/'commands.txt'; trace=root/'trace.jsonl'
            w.write_bytes(wad(arena() if geometry is None else geometry))
            f.write_text(''.join(' '.join(map(str,c))+'\n' for c in commands))
            p=subprocess.run([str(ROOT/'.lake/build/bin/trace-probe'),'E1M1',str(w),str(f)],capture_output=True,text=True)
            if not ok:
                self.assertNotEqual(p.returncode,0); return p
            self.assertEqual(p.returncode,0,p.stderr)
            trace.write_text(p.stdout)
            return dc.read_records(trace)

    def test_direct_turn_commands_bypass_keyboard_acceleration(self):
        cmds=[[0,0,-768,0],[0,0,32512,0],[0,0,-32768,0]]
        rows=self.trace(cmds)
        angle=rows[0]['state']['player']['angle']
        for row,cmd in zip(rows[1:],cmds):
            angle=(angle+cmd[2]*65536)&0xffffffff
            self.assertEqual(row['state']['player']['angle'],angle)
            self.assertEqual(row['command'],cmd)

    def test_arbitrary_forward_and_side_commands_are_not_keymask_approximations(self):
        # At angle zero, the original thrust is 2048 raw units per command unit
        # times the table cosine (65535/65536), with original fixed rounding.
        rows=self.trace([[17,-9,0,0]])
        a,b=[r['state']['player'] for r in rows]
        self.assertNotEqual((a['x'],a['y']),(b['x'],b['y']))
        slow=self.trace([[1,0,0,0]])[-1]['state']['player']
        fast=self.trace([[17,0,0,0]])[-1]['state']['player']
        self.assertGreater(fast['x']-a['x'],10*(slow['x']-a['x']))

    def test_shared_combat_consumes_ammo(self):
        rows=self.trace([[0,0,0,1]]*19)
        self.assertEqual(rows[0]['state']['player']['ammo'][0],50)
        self.assertEqual(rows[-1]['state']['player']['ammo'][0],49)

    def test_collected_map_actor_stays_removed_after_scene_resynchronization(self):
        geometry=arena(extras=[(0,0,0,2018,7),(96,0,0,2018,1)])
        rows=self.trace([[1,0,0,0]]+[[0,0,0,0]]*40,geometry)
        self.assertEqual(set(rows[0]['state']['actors']),{'1'})
        for row in rows[1:]:
            self.assertEqual(row['state']['actors'],{})
            self.assertEqual(row['state']['player']['armor'],100)

    def test_firing_uses_new_angle_but_pre_movement_position(self):
        prefix=[[0,0,0,0]]*40+[[0,0,0,1]]*4
        standing=self.trace(prefix+[[0,0,1024,1]])[-1]['state']
        moving=self.trace(prefix+[[17,-9,1024,1]])[-1]['state']
        unturned=self.trace(prefix+[[0,0,0,1]])[-1]['state']
        self.assertEqual(len(moving['impacts']),1)
        self.assertEqual(moving['impacts'],standing['impacts'])
        self.assertNotEqual(moving['player']['x'],standing['player']['x'])
        self.assertNotEqual(moving['impacts'],unturned['impacts'])
        self.assertEqual(moving['player']['ammo'][0],49)

    def test_movement_pickup_cannot_lower_weapon_until_next_playerthink(self):
        geometry=arena(extras=[(0,0,0,2001,7)])
        rows=self.trace([[0,0,0,0]]*40+[[1,0,0,0],[0,0,0,0]],geometry)
        before,pickup,after=[r['state'] for r in rows[-3:]]
        self.assertEqual(before['player']['ammo'][1],0)
        self.assertEqual(pickup['player']['ammo'][1],8)
        self.assertEqual(pickup['player']['pendingWeapon'],2)
        self.assertEqual(pickup['weapon']['state'],10) # S_PISTOL, still ready.
        self.assertEqual(after['weapon']['state'],11) # S_PISTOLDOWN next tic.

    def test_repeatable_trace_and_duplicate_position_actor_identities(self):
        geometry=arena([(96,0,0,3004,7),(96,0,0,3004,7)])
        a=self.trace([[0,0,0,0]]*3,geometry); b=self.trace([[0,0,0,0]]*3,geometry)
        self.assertEqual(a,b)
        self.assertEqual(set(a[0]['state']['actors']),{'1','2'})

    def test_bad_command_causes_explicit_failure(self):
        for command in [[0,0,1,0],[0,0,0,128],[0,0,0,28],[128,0,0,0]]:
            with self.subTest(command=command): self.trace([command],ok=False)

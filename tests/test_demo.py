"""Theorem trust audit and live telemetry integration with real Lean ticks."""
import importlib.util
import json
import pathlib
import re
import subprocess
import tempfile
import threading
import unittest
import urllib.error
import urllib.request
from test_combat import arena
from test_wad import wad
from test_things import things, sectors
from test_render import two_rooms
from test_hitscan import wall_scene

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('doom_demo', ROOT/'scripts/demo.py')
demo = importlib.util.module_from_spec(spec)
spec.loader.exec_module(demo)

class DemoTests(unittest.TestCase):
    def snapshot(self, script, geometry=None):
        with tempfile.TemporaryDirectory() as folder:
            path = pathlib.Path(folder)/'fixture.wad'
            path.write_bytes(wad(arena() if geometry is None else geometry))
            result = subprocess.run([str(ROOT/'.lake/build/bin/demo-probe'), 'E1M1', str(path), script],
                                    check=True, text=True, capture_output=True)
            return json.loads(result.stdout.splitlines()[-1])

    def test_kernel_audit_has_only_standard_axioms(self):
        result = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', 'ProofAudit.lean'],
                                cwd=ROOT, check=True, text=True, capture_output=True)
        lines = result.stdout.strip().splitlines()
        self.assertEqual(len(lines), 22, result.stdout)
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for line in lines:
            match = re.search(r'depends on axioms: \[(.*)\]', line)
            if match:
                self.assertLessEqual(set(match[1].split(', ')), allowed)
            else:
                self.assertIn('does not depend on any axioms', line)

    def test_pistol_discharge_records_actual_ammo_and_trace(self):
        self.assertIsNone(self.snapshot('4:8192')['weapon']['lastFire'])
        s = self.snapshot('5:8192')
        self.assertEqual(s['weapon']['lastFire'], dict(gun='pistol', tic=5, before=50, after=49, expected=1, traced=1))
        self.assertEqual(s['weapon']['bullets'], 49)
        second = self.snapshot('19:8192')['weapon']['lastFire']
        self.assertEqual((second['tic'], second['before'], second['after']), (19,49,48))

    def test_shotgun_pickup_and_seven_completed_traces(self):
        geometry = arena(extras=[(0,0,0,2001,7)])
        a = self.snapshot('1:2,31:0,4:8192', geometry)['weapon']
        b = self.snapshot('1:2,31:0,41:8192', geometry)['weapon']
        self.assertEqual(a['lastFire'], dict(gun='shotgun', tic=36, before=8, after=7, expected=7, traced=7))
        self.assertEqual((a['bullets'], a['shells']), (50,7))
        self.assertEqual(b['lastFire']['tic']-a['lastFire']['tic'], b['shotgunCycle'])

    def test_friction_samples_are_real_post_collision_values(self):
        for keys in [2,4,8,16,514,530]:
            with self.subTest(keys=keys):
                s=self.snapshot(f'10:{keys}')
                f=s['movement']['friction']
                self.assertIsNotNone(f)
                self.assertEqual(s['movement']['live'], f['after'])
                for component in ('x','y'):
                    self.assertEqual(f['after'][component], f['before'][component]*59392//65536)
                for side in ('before','after'):
                    v=f[side]
                    self.assertEqual(int(v['squared']), v['x']**2+v['y']**2)
                self.assertLessEqual(int(f['after']['squared']),int(f['before']['squared']))
        # At an axis-aligned wall collision zeroes X before friction is observed.
        blocked=self.snapshot('100:2')['movement']['friction']
        if blocked is not None:
            self.assertEqual(blocked['before']['x'], 0)

    def test_reset_clears_old_shot_and_movement_samples(self):
        s=self.snapshot('10:2,5:8192,1:1024')
        self.assertIsNone(s['weapon']['lastFire'])
        self.assertIsNone(s['movement']['friction'])
        self.assertEqual(s['weapon']['bullets'],50)

    def test_autoaim_records_clipped_target_and_original_negative_rounding(self):
        flat=self.snapshot('5:8192',arena([(96,0,0,3004,7)]))['aim']
        w=flat['window']
        self.assertLess(flat['slope'],0)
        self.assertEqual(w['bottom'],max(w['targetBottom'],w['portalBottom']))
        self.assertEqual(w['top'],min(w['targetTop'],w['portalTop']))
        self.assertLessEqual(w['bottom'],flat['slope'])
        self.assertLessEqual(flat['slope'],w['top'])
        geometry=things(sectors(two_rooms(),first=(0,64),second=(24,128)),[(0,0,0,1,7),(96,0,0,3004,7)])
        clipped=self.snapshot('5:8192',geometry)['aim']; w=clipped['window']
        self.assertLess(w['top'],w['targetTop'])
        self.assertEqual(w['top'],w['portalTop'])
        self.assertGreater(len(w['portals']),0)
        self.assertEqual(clipped['slope'],(w['bottom']+w['top'])//2)

    def test_side_probe_does_not_redirect_the_pistol_horizontally(self):
        for y,offset in [(24,0x04000000),(-24,0xfc000000)]:
            with self.subTest(y=y):
                aim=self.snapshot('5:8192',arena([(160,y,0,3004,7)]))['aim']
                self.assertIsNotNone(aim['window'])
                self.assertEqual(aim['offset'],offset)
                self.assertEqual(aim['pelletAngles'],[aim['facing']])
        a=self.snapshot('5:8192',wall_scene())['aim']
        self.assertIsNone(a['window'])
        self.assertEqual(a['slope'],0)
        self.assertIsNone(self.snapshot('5:8192,1:1024')['aim'])

    def test_shotgun_keeps_shared_autoaim_slope_and_seven_actual_angles(self):
        geometry=arena([(160,0,0,3004,7)],extras=[(0,0,0,2001,7)])
        aim=self.snapshot('1:2,31:0,4:8192',geometry)['aim']
        self.assertIsNotNone(aim['window'])
        self.assertEqual(len(aim['pelletAngles']),7)
        self.assertGreater(len(set(aim['pelletAngles'])),1)

    def test_displayed_source_is_valid_lean_with_real_observed_values(self):
        cases = [
            ('1:0',arena()),
            ('10:2,5:8192',arena()),
            ('10:4',arena()),
            ('5:8192',arena([(96,0,0,3004,7)])),
            ('5:8192',things(sectors(two_rooms(),first=(0,64),second=(24,128)),[(0,0,0,1,7),(96,0,0,3004,7)])),
            ('5:8192',arena([(160,24,0,3004,7)])),
            ('1:2,31:0,4:8192',arena([(160,0,0,3004,7)],extras=[(0,0,0,2001,7)])),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path=pathlib.Path(directory)/'LiveProof.lean'
            for script,geometry in cases:
                with self.subTest(script=script):
                    snapshot=self.snapshot(script,geometry)
                    path.write_text(snapshot['source'])
                    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],
                                          cwd=ROOT,text=True,capture_output=True)
                    self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_companion_transport_waiting_running_stopped_and_allowlist(self):
        with tempfile.TemporaryDirectory() as folder:
            path=pathlib.Path(folder)/'state.json'
            httpd=demo.server(path)
            worker=threading.Thread(target=httpd.serve_forever,daemon=True); worker.start()
            base=f'http://127.0.0.1:{httpd.server_port}'
            try:
                def read(route):
                    with urllib.request.urlopen(base+route) as response:
                        return response.read()
                self.assertIsNone(json.loads(read('/state'))['state'])
                state=self.snapshot('5:8192'); path.write_text(json.dumps(state))
                response=json.loads(read('/state'))
                self.assertEqual(response['state'], state)
                self.assertLess(response['age'],2)
                path.write_text('{"schema":1,"status":"stopped"}')
                self.assertEqual(json.loads(read('/state'))['state']['status'],'stopped')
                self.assertIn(b'friction_speed_squared',read('/proof/movement'))
                for route in ['/../README.md','/Viewer.lean','/state.json']:
                    with self.assertRaises(urllib.error.HTTPError) as error: read(route)
                    self.assertEqual(error.exception.code,404)
                    error.exception.close()
            finally:
                httpd.shutdown(); httpd.server_close(); worker.join()

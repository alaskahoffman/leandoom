"""Opt-in integration and mutation checks for the initialized boundary."""
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
OUT = ROOT / 'artifacts/initialized-e1m1'

class InitializedBoundary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        OUT.mkdir(parents=True,exist_ok=True)
        subprocess.run(['./scripts/lake','build','initialized-e1m1-probe'],cwd=ROOT,
                       capture_output=True,text=True,check=True,timeout=500)
        run=subprocess.run(['.lake/build/bin/initialized-e1m1-probe',
            'artifacts/doom-shareware-1.9/doom1.wad'],cwd=ROOT,
            capture_output=True,text=True,check=True,timeout=120)
        (OUT/'lean-initial.json').write_text(run.stdout)

    def test_production_initialization(self):
        build = subprocess.run(['./scripts/lake', 'build', 'initialized-e1m1-probe'],
                               cwd=ROOT, text=True, capture_output=True, timeout=500)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        run = subprocess.run(['.lake/build/bin/initialized-e1m1-probe',
                              'artifacts/doom-shareware-1.9/doom1.wad'], cwd=ROOT,
                             text=True, capture_output=True, timeout=120)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        state = json.loads(run.stdout)
        self.assertEqual(state['boundary'], 'Engine.start true false, before advance/afterPresent')
        self.assertEqual(state['record']['tick'], 0)
        self.assertEqual(state['width'], 36)
        self.assertEqual(state['height'], 23)
        self.assertEqual(len(state['lines']), 475)
        self.assertTrue(state['previousHeap'])
        (OUT/'lean-initial.json').write_text(run.stdout)

    def test_checked_relation(self):
        run = subprocess.run([sys.executable, 'scripts/verify_initialized_e1m1.py'],
                             cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        report = json.loads((OUT/'relation.json').read_text())
        self.assertEqual(report['status'], 'checked-initial-data')
        self.assertEqual(report['lines'], 475)
        self.assertEqual(report['cells'], 828)
        self.assertGreater(report['actors'], 1)
        self.assertEqual(report['epoch'], 1)

    def test_kernel_bridge(self):
        run = subprocess.run(['./scripts/lake', 'env', 'lean',
                              'tests/reference/initialized-e1m1.lean'],
                             cwd=ROOT, text=True, capture_output=True, timeout=240)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)

    def test_production_bridge_checker(self):
        import struct
        cap=OUT/'capture'
        meta=json.loads((cap/'initial.json').read_text())
        raw=(cap/'ram.bin').read_bytes()
        rd=lambda a: struct.unpack_from('<I',raw,a)[0]
        d=meta['data_linear']; p=rd(d+0x2ae78); lines=rd(d+0x2c120)
        data={'actor':[rd(p+off) for off in [12,16,20,68]],
              'epoch':rd(d+0x13580),'stamps':[rd(lines+62*i+54) for i in range(475)]}
        def check(value):
            path=OUT/'bridge-input.json'; path.write_text(json.dumps(value))
            run=subprocess.run(['.lake/build/bin/initialized-e1m1-probe',
                'artifacts/doom-shareware-1.9/doom1.wad',str(path)],cwd=ROOT,
                text=True,capture_output=True,timeout=120)
            self.assertEqual(run.returncode,0,run.stderr)
            return json.loads(run.stdout)
        actual=check(data)
        self.assertTrue(actual['engineCheck'])
        self.assertTrue(actual['startCheck'])
        self.assertTrue(actual['stampCheck'])
        (OUT/'lean-checked.json').write_text(json.dumps(actual))
        import copy
        wrong=copy.deepcopy(data); wrong['actor'][3]+=1
        self.assertFalse(check(wrong)['engineCheck'])
        wrong=copy.deepcopy(data); wrong['stamps'][474]=data['epoch']+1
        self.assertFalse(check(wrong)['stampCheck'])
        check(data) # Leave the genuine captured input for independent replay.

    def test_mutated_executed_aim_code_rejected(self):
        import verify_initialized_e1m1 as v
        raw=bytearray((OUT/'capture/ram.bin').read_bytes())
        meta=json.loads((OUT/'capture/initial.json').read_text())
        raw[meta['code_linear']+0x2bba0] ^= 1
        with self.assertRaisesRegex(ValueError,'code image'):
            v.validate(bytes(raw),meta,json.loads((OUT/'lean-initial.json').read_text()),
                       (OUT/'capture/dos/DOOM1.WAD').read_bytes())

    def test_capture_certificate(self):
        run=subprocess.run([sys.executable,'scripts/verify_initialized_e1m1.py','--kernel'],
                           cwd=ROOT,text=True,capture_output=True,timeout=240)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        self.assertTrue((OUT/'Captured.lean').exists())
        report=json.loads((OUT/'kernel-audit.json').read_text())
        self.assertEqual(report['status'],'pass')
        self.assertGreaterEqual(report['declarations'],5)

    def test_reordered_thinkers_rejected(self):
        import struct
        import verify_initialized_e1m1 as v
        raw=bytearray((OUT/'capture/ram.bin').read_bytes())
        meta=json.loads((OUT/'capture/initial.json').read_text())
        rd=lambda a:struct.unpack_from('<I',raw,a)[0]
        wr=lambda a,x:struct.pack_into('<I',raw,a,x)
        sentinel=meta['data_linear']+0x2cf74
        a=rd(sentinel+4); b=rd(a+4); c=rd(b+4)
        wr(sentinel+4,b); wr(b,sentinel); wr(b+4,a); wr(a,b); wr(a+4,c); wr(c,a)
        with self.assertRaisesRegex(ValueError,'thinker order'):
            v.validate(bytes(raw),meta,json.loads((OUT/'lean-initial.json').read_text()),
                       (OUT/'capture/dos/DOOM1.WAD').read_bytes())

    def test_mutation_matrix(self):
        import copy, struct
        import verify_initialized_e1m1 as v
        raw=(OUT/'capture/ram.bin').read_bytes()
        meta=json.loads((OUT/'capture/initial.json').read_text())
        lean=json.loads((OUT/'lean-initial.json').read_text())
        wad=(OUT/'capture/dos/DOOM1.WAD').read_bytes()
        r=json.loads((OUT/'relation.json').read_text()); p=r['placement']
        def raw_word(addr,value):
            b=bytearray(raw); struct.pack_into('<I',b,addr,value & 0xffffffff); return bytes(b)
        cases={
          'width': raw_word(p['data']+0x2c0fc,35),
          'origin': raw_word(p['data']+0x2c104,0),
          'offsetPointer': raw_word(p['data']+0x2c100,p['blockmap']),
          'lineDx': raw_word(p['lines']+8,123),
          'stamp': raw_word(p['lines']+54,r['epoch']+1),
          'epochWrap': raw_word(p['data']+0x13580,0xffffffff),
          'rng': raw_word(p['data']+0x12720,0),
          'playerHeight': raw_word(p['player']+68,0),
          'playerFlags': raw_word(p['player']+104,0),
          'playerAngle': raw_word(p['player']+32,0),
          'playerBacklink': raw_word(p['player']+132,0),
          'blockHead': raw_word(p['blocklinks'],p['player']),
          'thinkerCycle':raw_word(p['player']+4,p['player']),
          'boundaryBytes':raw_word(p['code']+0x2081a,0)}
        for name,b in cases.items():
            with self.subTest(name=name), self.assertRaises(ValueError): v.validate(b,meta,lean,wad)
        for name in ['lineOrder','actorOrder','shape','phase','postWipeRng']:
            value=copy.deepcopy(lean)
            if name=='lineOrder':
                i=next(i for i,c in enumerate(value['cells']) if len(set(c))>1)
                value['cells'][i].reverse()
            elif name=='actorOrder':
                i=next(i for i,c in enumerate(value['links']) if len(c)>1)
                value['links'][i].reverse()
            elif name=='shape': value['links'].pop()
            elif name=='phase': value['phase']=1
            else: value['record']['state']['rng']['misc']=1
            with self.subTest(name=name), self.assertRaises(ValueError): v.validate(raw,meta,value,wad)
        for key,value in [('pc',0x2082e),('paging',True),('ds_base',1),('tick',1)]:
            bad=dict(meta); bad[key]=value
            with self.subTest(name=key),self.assertRaises(ValueError): v.validate(raw,bad,lean,wad)
        with self.assertRaises(ValueError): v.validate(raw,meta,lean,wad[:-1])
        good=(OUT/'kernel.log').read_text()
        v.audit(good)
        for bad in [good.replace('propext','sorryAx',1),good.splitlines()[0],good+good]:
            with self.assertRaises(ValueError): v.audit(bad)

    def test_kernel_certificate_mutation_rejected(self):
        import tempfile, os
        text=(OUT/'Captured.lean').read_text().replace('def stamps : Array Nat := #[0,',
                                                     'def stamps : Array Nat := #[2,',1)
        self.assertNotEqual(text,(OUT/'Captured.lean').read_text())
        with tempfile.TemporaryDirectory(dir=os.environ['TMPDIR']) as tmp:
            path=Path(tmp)/'Mutated.lean'; path.write_text(text)
            run=subprocess.run(['./scripts/lake','env','lean',str(path)],cwd=ROOT,
                               text=True,capture_output=True,timeout=180)
        self.assertNotEqual(run.returncode,0)
        self.assertIn('error:',run.stdout)
        (OUT/'kernel-negative.log').write_text(run.stdout+run.stderr)

    def test_actual_capture(self):
        run = subprocess.run([str(ROOT/'.tools/x86-check/bin/python'), 'scripts/capture_initialized_e1m1.py'],
                             cwd=ROOT, text=True, capture_output=True, timeout=580)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        meta = json.loads((OUT/'capture/initial.json').read_text())
        self.assertEqual(meta['pc'], 0x2081a)
        self.assertEqual(meta['tick'], 0)
        self.assertEqual(meta['leveltime'], 0)
        self.assertFalse(meta['paging'])
        self.assertEqual((OUT/'capture/ram.bin').stat().st_size, 32*1024*1024)
        trace = json.loads((OUT/'capture/original.jsonl').read_text().splitlines()[0])
        self.assertEqual(trace['tick'], 0)
        self.assertIsNone(trace['command'])

if __name__ == '__main__':
    unittest.main()

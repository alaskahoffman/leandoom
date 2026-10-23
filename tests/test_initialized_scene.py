"""Actual retained capture, production initializer and typed scene bridge."""
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'artifacts/initialized-e1m1-scene'
sys.path.insert(0,str(ROOT/'scripts'))

class InitializedScene(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Every test (including a negative test selected alone) gets freshly
        # authenticated inputs and a valid kernel certificate before mutation.
        run=subprocess.run([sys.executable,'scripts/verify_initialized_scene.py','--kernel'],
                           cwd=ROOT,text=True,capture_output=True,timeout=800)
        if run.returncode!=0:
            raise RuntimeError(run.stdout+run.stderr)

    def test_prepare_without_historical_manifest(self):
        from unittest.mock import patch
        import verify_initialized_scene as v
        historical=v.old.OUT/'validation.json'
        read_bytes=Path.read_bytes
        def without_historical(path):
            if path==historical:
                raise FileNotFoundError('historical validation.json is not a capture prerequisite')
            return read_bytes(path)
        # Simulate a clean reproduction without deleting retained evidence.
        # Authentication/extraction remain real; only the incidental read is blocked.
        with patch.object(Path,'read_bytes',without_historical):
            data,rows=v.prepare()
        report=json.loads((OUT/'extraction.json').read_text())
        hashes=report['sourceHashes']
        self.assertNotIn(str(historical.relative_to(ROOT)),hashes)
        for path in [Path(v.__file__),Path(v.old.__file__),v.CAP/'provenance.json',
                     v.old.OUT/'lean-initial.json',OUT/'input.json']:
            self.assertEqual(hashes[str(path.relative_to(ROOT))],v.old.oc.sha(path.read_bytes()))
        self.assertEqual(report['pointer_slots'],len(rows))
        self.assertEqual(report['raw_sha256'],v.old.oc.sha((v.CAP/'ram.bin').read_bytes()))
        self.assertEqual(report['canonical_sha256'],v.old.oc.sha((OUT/'canonical.bin').read_bytes()))
        self.assertEqual(data,json.loads((OUT/'input.json').read_text()))

    def test_actual_production_scene(self):
        result=json.loads((OUT/'checked.json').read_text())
        self.assertTrue(result['sceneCheck'])
        self.assertTrue(result['startCheck'])
        self.assertEqual(result['cells'],828)
        self.assertEqual(result['lines'],475)
        self.assertTrue(result['previousHeap'])
        self.assertTrue(result.get('layoutCheck',False), 'finite layout check missing')

    def test_oversized_mapping_literal_rejected(self):
        import copy, os, tempfile
        import verify_initialized_scene as v
        data=json.loads((OUT/'input.json').read_text())
        bad=copy.deepcopy(data); bad['pointers'][0]+=2**32
        with tempfile.TemporaryDirectory(dir=os.environ['TMPDIR']) as tmp:
            path=Path(tmp)/'input.json'; path.write_text(json.dumps(bad))
            try:
                result=v.run_probe(input_path=path)
            except ValueError:
                return
            self.assertFalse(result['sceneCheck'], 'oversized pointer was silently truncated')

    def test_mutations(self):
        import copy, os, struct, tempfile
        import verify_initialized_scene as v
        data=json.loads((OUT/'input.json').read_text())
        raw=(v.CAP/'ram.bin').read_bytes(); canonical=(OUT/'canonical.bin').read_bytes()
        lean=json.loads((v.old.OUT/'lean-initial.json').read_text())
        d=data['dataBase']; line=data['lines']; player=data['pointers'][0]
        rd=lambda b,a:struct.unpack_from('<I',b,a)[0]
        def word(b,a,value):
            b=bytearray(b); struct.pack_into('<I',b,a,value & 0xffffffff); return bytes(b)
        cases=[]
        # A scalar changed consistently in both images still fails production geometry.
        cases.append(('line-scalar',word(raw,d+line+8,123),word(canonical,line+8,123),data))
        cases.append(('raw-only-scalar',word(raw,d+player+12,123),canonical,data))
        cases.append(('canonical-only-scalar',raw,word(canonical,player+12,123),data))
        cases.append(('untranslated-pointer',raw,word(canonical,line,rd(raw,d+line)),data))
        cases.append(('wrong-pointer-target',word(raw,d+line,1),word(canonical,line,1),data))
        # A typed pointer changed consistently, but to the wrong vertex.
        other=rd(canonical,line+4)
        cases.append(('wrong-vertex',word(raw,d+line,d+other),word(canonical,line,other),data))
        bad=copy.deepcopy(data); bad['pointers'][0]=bad['pointers'][next(i for i,p in enumerate(bad['pointers']) if i and p)]
        cases.append(('identity-map',raw,canonical,bad))
        bad=copy.deepcopy(data); bad['words'][4]+=1
        cases.append(('offset-table',raw,canonical,bad))
        bad=copy.deepcopy(data); off=bad['words'][4]; bad['words'][off]=1
        cases.append(('leading-zero',raw,canonical,bad))
        # Reverse an actual multi-node list while preserving typed provenance.
        index,ids=next((i,ids) for i,ids in enumerate(lean['links']) if len(ids)>1)
        chain=[data['pointers'][i] for i in ids]
        reversed_chain=list(reversed(chain)); rr=raw; cc=canonical
        head=data['links']+4*index
        rr=word(rr,d+head,d+reversed_chain[0]); cc=word(cc,head,reversed_chain[0])
        for i,p in enumerate(reversed_chain):
            nxt=reversed_chain[i+1] if i+1<len(reversed_chain) else 0
            rr=word(rr,d+p+44,d+nxt if nxt else 0); cc=word(cc,p+44,nxt)
        cases.append(('bnext-order',rr,cc,data))
        cases.append(('back-null',word(raw,d+line+50,0),word(canonical,line+50,0),data)
                     if rd(canonical,line+50) else
                     ('back-nonnull',word(raw,d+line+50,d+rd(canonical,line)),
                      word(canonical,line+50,rd(canonical,line)),data))
        results={}
        with tempfile.TemporaryDirectory(dir=os.environ['TMPDIR']) as tmp:
            tmp=Path(tmp)
            for name,r,c,value in cases:
                with self.subTest(name=name):
                    (tmp/'raw.bin').write_bytes(r); (tmp/'canonical.bin').write_bytes(c)
                    (tmp/'input.json').write_text(json.dumps(value))
                    result=v.run_probe(tmp/'raw.bin',tmp/'canonical.bin',tmp/'input.json')
                    self.assertFalse(result['sceneCheck'],name)
                    self.assertFalse(result['startCheck'],name)
                    results[name]=result
        (OUT/'mutations.json').write_text(json.dumps(results,indent=2)+'\n')

    def test_kernel_certificate_mutation(self):
        import os, re, tempfile
        path=OUT/'CapturedPointers.lean'; text=path.read_text()
        changed=re.sub(r'(def rows0 : List Row := \[\(\d+,\d+,)(\d+)',
                       lambda m:m[1]+str(int(m[2])+1),text,count=1)
        self.assertNotEqual(text,changed)
        with tempfile.TemporaryDirectory(dir=os.environ['TMPDIR']) as tmp:
            bad=Path(tmp)/'BadPointers.lean'; bad.write_text(changed)
            run=subprocess.run(['./scripts/lake','env','lean',str(bad)],cwd=ROOT,
                               text=True,capture_output=True,timeout=180)
        self.assertNotEqual(run.returncode,0)
        self.assertIn('error:',run.stdout)
        (OUT/'kernel-negative.log').write_text(run.stdout+run.stderr)

    def test_guard_mutations(self):
        import copy, os, tempfile
        import verify_initialized_scene as v
        data=json.loads((OUT/'input.json').read_text())
        cases={
          'lines-overlap':(data['lines'],data['lines']+100),
          'global-overlap':(0x2c0f8,0x2c100),
          'blockmap-extra-two-bytes':(data['blockmap']+6922,data['blockmap']+6930)}
        results={}
        with tempfile.TemporaryDirectory(dir=os.environ['TMPDIR']) as tmp:
            path=Path(tmp)/'input.json'
            for name,(lo,hi) in cases.items():
                value=copy.deepcopy(data); value['guardStackLo']=lo; value['guardStackHi']=hi
                path.write_text(json.dumps(value))
                result=v.run_probe(input_path=path)
                self.assertTrue(result['sceneCheck'])
                self.assertFalse(result['layoutCheck'],name)
                results[name]=result
        (OUT/'guard-mutations.json').write_text(json.dumps(results,indent=2)+'\n')

    def test_strict_audit_mutations(self):
        import verify_initialized_scene as v
        report=json.loads((OUT/'kernel-audit.json').read_text())
        text=(OUT/'kernel.log').read_text(); v.audit(text,report['names'])
        for bad in [text.replace('propext','sorryAx',1),text.splitlines()[0],text+text]:
            with self.assertRaises(ValueError): v.audit(bad,report['names'])

    def test_kernel_contracts(self):
        for name in ['initialized-address','initialized-scene','initialized-scene-regions']:
            run=subprocess.run(['./scripts/lake','env','lean','tests/reference/'+name+'.lean'],
                               cwd=ROOT,text=True,capture_output=True,timeout=180)
            self.assertEqual(run.returncode,0,run.stdout+run.stderr)

    def test_pointer_certificate(self):
        import verify_initialized_scene as v
        self.assertTrue(hasattr(v,'certificate'), 'kernel pointer certificate missing')
        data,rows=v.prepare()
        report=v.certificate(data,rows)
        self.assertEqual(report['status'],'pass')
        self.assertEqual(report['pointerSlots'],len(rows))

if __name__=='__main__': unittest.main()

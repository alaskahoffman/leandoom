#!/usr/bin/env python3
"""Opt-in typed captured-address extraction. Never overwrites the raw capture.
Only enumerated pointer fields change representation. All other bytes are copied
unchanged; the Lean checker independently verifies every consumed typed read.
This is not an x86 execution-relocation theorem or a whole RAM equivalence.
"""
import json
from pathlib import Path
import struct
import subprocess
import sys
sys.setrecursionlimit(10000)
import verify_initialized_e1m1 as old

ROOT=old.ROOT
OUT=ROOT/'artifacts/initialized-e1m1-scene'
CAP=old.OUT/'capture'
require=old.require

def extract(raw, meta, relation, lean):
    d=meta['data_linear']; m=old.RAM(raw)
    require(0x100000<=d<len(raw),'data base')
    p=relation['placement']
    require(p['data']==d,'placement data base')
    ptrs={int(k):v for k,v in relation['actorPointers'].items()}
    # This whitelist is a schema, not a heuristic testing whether a scalar looks
    # like an address. Front-sector pointers are included for later portal work.
    sites={d+a for a in [0x2c100,0x2c10c,0x2c120,0x2c0f8]}
    sites.update(p['lines']+62*i+off for i in range(475) for off in [0,4,46,50])
    sites.update(p['blocklinks']+4*i for i in range(828))
    sites.update(v+44 for v in ptrs.values())
    canonical=bytearray(raw[d:]); rows=[]
    def offset(value):
        if value==0: return 0
        require(d<value<len(raw),'pointer target outside canonical data RAM')
        return value-d
    for site in sorted(sites):
        value=m.u32(site); translated=offset(value)
        require(d<=site<=len(raw)-4,'pointer slot range')
        struct.pack_into('<I',canonical,site-d,translated)
        rows.append({'address':site-d,'raw':value,'canonical':translated})
    pointers=[0]*len(lean['things'])
    for identity,value in ptrs.items():
        require(0<=identity<len(pointers),'actor identity mapping')
        pointers[identity]=offset(value)
    data={'dataBase':d,'blockmap':offset(p['blockmap']),'lines':offset(p['lines']),
          'links':offset(p['blocklinks']),'words':relation['blockmapWords'],'pointers':pointers,
          'guardStackLo':0x80000,'guardStackHi':0x90000,
          'guardScope':'chosen envelope only; future aim ESP reserve is NOT established'}
    return bytes(canonical),data,rows

def prepare():
    # Existing authentication performs no writes when called as a library.
    relation=old.verify_files()
    raw=(CAP/'ram.bin').read_bytes()
    meta=json.loads((CAP/'initial.json').read_text())
    lean=json.loads((old.OUT/'lean-initial.json').read_text())
    canonical,data,rows=extract(raw,meta,relation,lean)
    OUT.mkdir(exist_ok=True)
    (OUT/'canonical.bin').write_bytes(canonical)
    (OUT/'input.json').write_text(json.dumps(data,indent=2)+'\n')
    (OUT/'pointer-rows.json').write_text(json.dumps(rows,indent=2)+'\n')
    (OUT/'extraction.json').write_text(json.dumps({
        'scope':'typed finite incoming scene reads only; not execution relocation',
        'raw_sha256':old.oc.sha(raw),'canonical_sha256':old.oc.sha(canonical),
        # Bind the live authenticated inputs, not an optional historical report.
        'pointer_slots':len(rows),'sourceHashes':{**relation['sourceHashes'],
        **{str(p.relative_to(ROOT)):old.oc.sha(p.read_bytes())
        for p in [Path(__file__),CAP/'provenance.json',OUT/'input.json']}}},indent=2)+'\n')
    return data,rows

def run_probe(raw_path=CAP/'ram.bin',canonical_path=OUT/'canonical.bin',input_path=OUT/'input.json'):
    run=subprocess.run(['.lake/build/bin/initialized-scene-probe',str(CAP/'dos/DOOM1.WAD'),
                        str(raw_path),str(canonical_path),str(input_path)],cwd=ROOT,
                       text=True,capture_output=True,timeout=180)
    require(run.returncode==0,run.stdout+run.stderr)
    return json.loads(run.stdout)

AUDITED = ['Doom.Proofs.InitializedAddress.'+n for n in
    ['sound','encodes','pointer_translation','scalar_preserved','rows_sound','rows_append',
     'address_exact','pointer_reconstruct']] + [
    'Doom.Proofs.InitializedScene.'+n for n in
    ['map_values','line_words','node_words','cell_payload','cell_scene_lines','fraction_check',
     'cell_sources','scene_sound','started_scene']] + [
    'Doom.Proofs.InitializedSceneRegions.'+n for n in
    ['storage','cell_layout','map_layout','cell_safe','map_inputs']]

def audit(text,names):
    import re
    require('error:' not in text and 'warning:' not in text,'Lean diagnostics')
    rows=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
    require([n for n,_ in rows]==names,'strict audit declaration coverage')
    for name,axioms in rows:
        require(set(filter(None,(a.strip() for a in axioms.split(',')))) <=
                {'propext','Quot.sound','Classical.choice'},'forbidden axiom '+name)
    return {'status':'pass','declarations':len(rows),'names':names}

def certificate(data,rows):
    # Check observed values against both files again, rather than certifying a
    # caller-supplied arithmetic table disconnected from retained memory.
    raw=(CAP/'ram.bin').read_bytes(); canonical=(OUT/'canonical.bin').read_bytes()
    for row in rows:
        require(struct.unpack_from('<I',raw,data['dataBase']+row['address'])[0]==row['raw'],'raw row decode')
        require(struct.unpack_from('<I',canonical,row['address'])[0]==row['canonical'],'canonical row decode')
    chunks=[rows[i:i+64] for i in range(0,len(rows),64)]
    text='''import Doom.Proofs.InitializedSceneRegions
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace CapturedScene
open Doom.Verification Doom.Verification.X86Memory Doom.Proofs.InitializedAddress
-- Actual extracted pointer reads only, not fabricated original RAM.
-- Read decoding is explicit; this is NOT execution relocation compatibility.
'''
    text+='-- raw SHA256: '+old.oc.sha(raw)+'\n-- canonical SHA256: '+old.oc.sha(canonical)+'\n'
    names=list(AUDITED)
    for i,chunk in enumerate(chunks):
        values=','.join('(%d,%d,%d)'%(r['address'],r['raw'],r['canonical']) for r in chunk)
        text+=f'def rows{i} : List Row := [{values}]\n'
        text+=f'theorem checked{i} : rowsCheck {data["dataBase"]} {len(raw)} rows{i}=true := by decide +kernel\n'
        names.append(f'CapturedScene.checked{i}')
    text+='def rows : List Row := '+ ' ++ '.join(f'rows{i}' for i in range(len(chunks)))+'\n'
    text+=f'theorem checked : rowsCheck {data["dataBase"]} {len(raw)} rows=true := by\n'
    proof=f'checked{len(chunks)-1}'
    for i in reversed(range(len(chunks)-1)):
        proof=f'(rows_append _ _ rows{i} _ checked{i} {proof})'
    text+='  unfold rows\n  exact '+proof+'\n'
    names.append('CapturedScene.checked')
    text+=f'''theorem decoded (raw canonical : Memory)
    (hr : ∀ r∈rows, load32 raw (BitVec.ofNat 32 {data['dataBase']}+BitVec.ofNat 32 r.1)=BitVec.ofNat 32 r.2.1)
    (hc : ∀ r∈rows, load32 canonical (BitVec.ofNat 32 r.1)=BitVec.ofNat 32 r.2.2) :
    ∀ r∈rows, Address {data['dataBase']} {len(raw)} (.pointer (BitVec.ofNat 32 r.1) (BitVec.ofNat 32 r.2.2)) ∧
      Observed raw canonical {data['dataBase']} {len(raw)} (.pointer (BitVec.ofNat 32 r.1) (BitVec.ofNat 32 r.2.2)) := by
  exact rows_sound _ _ rows checked raw canonical hr hc
end CapturedScene
'''
    names.append('CapturedScene.decoded')
    text+=''.join('#print axioms '+name+'\n' for name in names)
    path=OUT/'CapturedPointers.lean'; path.write_text(text)
    run=subprocess.run(['./scripts/lake','env','lean',str(path)],cwd=ROOT,
                       text=True,capture_output=True,timeout=240)
    log=run.stdout+run.stderr; (OUT/'kernel.log').write_text(log)
    require(run.returncode==0,'pointer certificate failed: '+log)
    result=audit(log,names); result['pointerSlots']=len(rows)
    (OUT/'kernel-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def main():
    run=subprocess.run(['./scripts/lake','build','initialized-scene-probe'],cwd=ROOT,
                       text=True,capture_output=True,timeout=480)
    OUT.mkdir(exist_ok=True)
    (OUT/'probe-build.log').write_text(run.stdout+run.stderr)
    require(run.returncode==0,'probe build failed: '+run.stdout+run.stderr)
    data,rows=prepare()
    result=run_probe()
    (OUT/'checked.json').write_text(json.dumps(result,indent=2)+'\n')
    require(result['sceneCheck'] and result['startCheck'] and result['layoutCheck'],
            'actual scene rejected: '+str(result))
    if '--kernel' in sys.argv: certificate(data,rows)
    print(json.dumps(result))

if __name__=='__main__': main()

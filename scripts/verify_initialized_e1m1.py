#!/usr/bin/env python3
"""Check actual initialized DOS data against production Engine.start projection.
Extraction and address interpretation are explicit trusted/empirical boundaries.
Never rewrites RAM, repairs ordering, or assumes a successful future aim query.
"""
import json
from pathlib import Path
import struct
import subprocess
import re
import sys
sys.setrecursionlimit(10000)
import original_demo_compare as oc

ROOT = oc.ROOT
OUT = ROOT/'artifacts/initialized-e1m1'
require = oc.require
PIN = json.loads((ROOT/'tests/reference/e1m1-proof-profile.json').read_text())

def lump(wad, name):
    count, directory = struct.unpack_from('<II', wad, 4)
    entries = [struct.unpack_from('<II8s',wad,directory+16*i) for i in range(count)]
    start = next(i for i,(_,_,n) in enumerate(entries) if n.rstrip(b'\0')==b'E1M1')
    p,n,_ = next(e for e in entries[start+1:start+11] if e[2].rstrip(b'\0')==name.encode())
    return wad[p:p+n]

class RAM:
    def __init__(self, data):
        require(len(data)==32*1024*1024,'RAM size')
        self.data=data
    def bytes(self, p, n):
        # Only ordinary mapped high RAM; never alias the device aperture.
        require(type(p) is int and 0x100000<=p<=len(self.data)-n,'RAM read range')
        return self.data[p:p+n]
    def u32(self,p): return int.from_bytes(self.bytes(p,4),'little')
    def i32(self,p): return int.from_bytes(self.bytes(p,4),'little',signed=True)
    def u16(self,p): return int.from_bytes(self.bytes(p,2),'little')

def validate_code(m, meta):
    image=oc.original_image()
    code,*_=oc.mul.inspect_image(image,oc.PROFILE)
    expected=bytearray(code)
    origins={1:meta['code_linear'],3:meta['data_linear']}
    ranges=[(0x2081a,0x20830),(0x24150,0x24190),(0x2b000,0x33500)]
    for p,kind,target in oc.fixups(image,range((len(code)+4095)//4096)):
        if kind in origins:
            struct.pack_into('<I',expected,p,(origins[kind]+target)&0xffffffff)
        else:
            require(not any(a<p+4 and p<b for a,b in ranges),'unsupported code relocation')
    for start,stop in ranges:
        require(m.bytes(meta['code_linear']+start,stop-start)==expected[start:stop],
                f'captured code image {start:x}..{stop:x}')
    return [{'start':a,'stop':b,'relocated_sha256':oc.sha(expected[a:b])} for a,b in ranges]

def validate(raw, meta, lean, wad):
    m=RAM(raw); d=meta['data_linear']; code=meta['code_linear']
    code_ranges=validate_code(m,meta)
    require(meta['pc']==0x2081a and meta['tick']==meta['leveltime']==0 and
            meta['paging'] is False and meta['ds_base']==meta['ss_base']==meta['cs_base']==0,
            'unsupported boundary/binding')
    require(meta['eip']==code+meta['pc'],'PC binding')
    require(m.bytes(code+0x2081a,22)==bytes.fromhex(oc.SPEC['signature_hex']),'boundary code bytes')
    for p,target in oc.SPEC['data_operands'].items():
        require(m.u32(code+int(p,16))==d+int(target,16),'relocated data binding')
    require(m.u32(d+0x2cf80)==0,'raw leveltime')
    require(lean['boundary']=='Engine.start true false, before advance/afterPresent' and
            lean['record']['tick']==0 and lean['record']['command'] is None and
            lean['phase']==0 and lean['previousHeap'] is True,'Lean boundary')
    require(oc.sha(wad)==PIN['wad_sha256'],'WAD pin')
    w,h=m.u32(d+0x2c0fc),m.u32(d+0x2c110)
    require((w,h)==(lean['width'],lean['height'])==(36,23),'dimensions')
    require(lean['vanillaOffsets'] is True,'vanilla offsets')
    require([m.i32(d+0x2c104),m.i32(d+0x2c108)]==[x*65536 for x in lean['origin']],'origin')
    base=m.u32(d+0x2c10c); lines=m.u32(d+0x2c120); links=m.u32(d+0x2c0f8)
    require(m.u32(d+0x2c100)==base+8,'offset table pointer')
    block=lump(wad,'BLOCKMAP')
    require(m.bytes(base,len(block))==block,'raw BLOCKMAP/WAD image')
    words=list(struct.unpack('<'+'H'*(len(block)//2),block))
    require(len(lean['cells'])==len(lean['links'])==w*h,'cell counts')
    for i,cell in enumerate(lean['cells']):
        off=words[4+i]; require(off<32768,'signed offset')
        ids=[]
        while off+len(ids)<len(words) and words[off+len(ids)]!=65535:
            ids.append(words[off+len(ids)])
            require(len(ids)<=13 and ids[-1]<475,'bounded cell IDs')
        require(off+len(ids)<len(words) and ids==[0]+cell,'ordered line list/sentinel')
    require(len(lean['lines'])==475,'line count')
    stamps=[]
    for i,line in enumerate(lean['lines']):
        p=lines+62*i; v=m.u32(p)
        got={'x':m.i32(v),'y':m.i32(v+4),'dx':m.i32(p+8),'dy':m.i32(p+12),
             'front':[m.i32(m.u32(p+46)),m.i32(m.u32(p+46)+4)],
             'back':None if not m.u32(p+50) else [m.i32(m.u32(p+50)),m.i32(m.u32(p+50)+4)],
             'blocking':bool(m.u16(p+16)&1),'twoSided':bool(m.u16(p+16)&4)}
        require(got==line,f'line geometry/portal {i}')
        stamps.append(m.u32(p+54))
    epoch=m.u32(d+0x13580)
    require(epoch<2**32-3 and all(s<=epoch for s in stamps),'stamp freshness bound')
    require(lean['record']['state']['rng']=={'play':m.u32(d+0x12720),'misc':m.u32(d+0x1271c)},'RNG')
    player=m.u32(d+0x2ae78)
    require(m.u32(player+132)==d+0x2ae78,'player backlink')
    require(m.u32(player+32)==lean['record']['state']['player']['angle'],'player angle')
    sentinel=d+0x2cf74; node=m.u32(sentinel+4); seen=set(); mapping={}; thinker_order=[]
    # Map by all original THINGS spawnpoint shorts, preserving duplicate occurrence order.
    remaining={i for i,t in enumerate(lean['spawnThings']) if
               (t[3]==1 or t[3]>4 and t[3]!=11 and not(t[4]&16) and bool(t[4]&2))}
    expected_order=[0 if lean['spawnThings'][i][3]==1 else i+1 for i in sorted(remaining)]
    while node!=sentinel:
        require(node not in seen and len(seen)<10000,'thinker cycle/bound')
        seen.add(node)
        require(m.u32(m.u32(node+4))==node,'thinker backlink')
        if m.u32(node+8)==m.u32(code+0x31643):
            if node==player:
                matches=[i for i in remaining if lean['spawnThings'][i][3]==1]; identity=0
            else:
                spawn=list(struct.unpack('<hhHHH',m.bytes(node+140,10)))
                matches=[i for i in sorted(remaining) if lean['spawnThings'][i]==spawn]
                identity=matches[0]+1 if matches else -1
            require(bool(matches),f'unknown mobj spawn {node:x}')
            remaining.remove(matches[0]); require(identity not in mapping,'duplicate actor identity')
            mapping[identity]=node; thinker_order.append(identity)
            t=lean['things'][identity]; flags=m.u32(node+104)
            for field,off in {'x':12,'y':16,'z':20,'radius':64,'height':68,'floor':56,'ceiling':60}.items():
                require(m.i32(node+off)==t[field],f'actor {identity} {field}')
            for field,mask in [('solid',2),('shootable',4),('noBlockmap',16)]:
                require(bool(flags&mask)==t[field],f'actor {identity} {field}')
            require(not t['removed'],f'removed live actor {identity}')
        node=m.u32(node+4)
    require(not remaining,'missing spawned actors')
    require(thinker_order==expected_order,'spawn thinker order')
    reverse={p:i for i,p in mapping.items()}
    for i,expected in enumerate(lean['links']):
        p=m.u32(links+4*i); actual=[]
        while p:
            require(p in reverse and reverse[p] not in actual,'unknown/cyclic blocklink')
            actual.append(reverse[p]); p=m.u32(p+44)
        require(actual==expected,f'blocklink order {i}')
    return {'status':'checked-initial-data','lines':len(stamps),'cells':w*h,'actors':len(mapping),
        'epoch':epoch,'codeRanges':code_ranges,'stamps':stamps,'blockmapWords':words,'actorPointers':mapping,
        'thinkerOrder':thinker_order,'placement':{'data':d,'code':code,'lines':lines,'blockmap':base,
        'blocklinks':links,'player':player,'stack':meta['registers'][4]},
        'rng':lean['record']['state']['rng'],
        'scope':'initial aiming data only; not full initial-state equivalence, future aim success or preservation'}

def verify_files():
    cap=OUT/'capture'; evidence=json.loads((cap/'provenance.json').read_text())
    for name,key in [('ram.bin','raw_ram_sha256'),('vram.bin','raw_vram_sha256'),
                     ('initial.json','metadata_sha256'),('original.jsonl','trace_sha256'),
                     ('dosbox.conf','config_sha256')]:
        require(oc.sha((cap/name).read_bytes())==evidence[key],f'{name} hash binding')
    for name,key in [('DOOM.EXE','exe_sha256'),('DOOM1.WAD','wad_sha256')]:
        require(oc.sha((cap/'dos'/name).read_bytes())==evidence[key]==PIN[key],f'{name} pin')
    require(oc.sha((cap/'dos/INPUT.LMP').read_bytes())==evidence['demo_sha256'],'demo binding')
    require(oc.dc.decode_demo((cap/'dos/INPUT.LMP').read_bytes())==[[0,0,0,0]],'commands')
    oc.original_image()  # Existing byte/relocation evidence authentication.
    for p,h in evidence['build']['inputs'].items():
        if p in ('archive','configure'): continue
        require(oc.sha((ROOT/p).read_bytes())==h,f'capture source binding {p}')
    lean=json.loads((OUT/'lean-initial.json').read_text())
    result=validate((cap/'ram.bin').read_bytes(),json.loads((cap/'initial.json').read_text()),
                    lean,(cap/'dos/DOOM1.WAD').read_bytes())
    # Independent existing trace observer, a second extraction path for shared fields.
    original=json.loads((cap/'original.jsonl').read_text().splitlines()[0])
    for key,value in original['state'].items():
        target=lean['record']['state'][key]
        if key=='player': target={k:target[k] for k in value}
        require(value==target,f'independent initial trace {key}')
    result['sourceHashes']={str(p.relative_to(ROOT)):oc.sha(p.read_bytes()) for p in
       [Path(__file__), ROOT/'InitializedE1M1Probe.lean', OUT/'lean-initial.json',cap/'provenance.json']}
    return result

AUDITED=['Doom.Proofs.InitializedE1M1.'+n for n in
         ['supported_of_check','fresh_pair','engine_inputs','started_inputs']]+['CapturedInitial.checked','CapturedInitial.before_pair']

def audit(text):
    require('error:' not in text and 'warning:' not in text,'Lean audit diagnostics')
    rows=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
    require([n for n,_ in rows]==AUDITED,'strict audit declaration coverage')
    for name,axioms in rows:
        require(set(filter(None,(a.strip() for a in axioms.split(',')))) <=
                {'propext','Quot.sound','Classical.choice'},f'forbidden axiom {name}')
    return {'status':'pass','declarations':len(rows),'names':AUDITED}

def certificate(result):
    values='#['+','.join(map(str,result['stamps']))+']'
    epoch=result['epoch']
    text=f'''import Doom.Proofs.InitializedE1M1
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
-- Extracted from actual captured RAM, not generated gameplay data.
-- Raw provenance: {oc.sha((OUT/'capture/provenance.json').read_bytes())}
-- Decoding/address interpretation remains an explicit boundary premise.
namespace CapturedInitial
open Doom Doom.Verification Doom.Verification.X86Memory Doom.Proofs
 def stamps : Array Nat := {values}
 theorem checked : InitializedE1M1.stampCheck stamps {epoch} = true := by decide +kernel
 theorem before_pair (m : Memory) (lines : Word)
     (decoded : ∀ j<475, load32 m (OriginalLineVisits.stamp lines j) =
       BitVec.ofNat 32 stamps[j]!) :
     E1M1AimStampImage.Fresh m lines (BitVec.ofNat 32 {epoch}+1) 475 ∧
     E1M1AimStampImage.Fresh m lines ((BitVec.ofNat 32 {epoch}+1)+1) 475 := by
   exact InitializedE1M1.fresh_pair stamps {epoch} m lines checked decoded
end CapturedInitial
'''
    text+=''.join('#print axioms '+name+'\n' for name in AUDITED)
    path=OUT/'Captured.lean'; path.write_text(text)
    run=subprocess.run(['./scripts/lake','env','lean',str(path)],cwd=ROOT,
                       text=True,capture_output=True,timeout=180)
    log=run.stdout+run.stderr
    (OUT/'kernel.log').write_text(log)
    require(run.returncode==0,'captured kernel certificate failed: '+log)
    report=audit(log)
    (OUT/'kernel-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

def main():
    result=verify_files()
    (OUT/'relation.json').write_text(json.dumps(result,indent=2)+'\n')
    if '--kernel' in sys.argv: certificate(result)
    print(json.dumps({k:result[k] for k in ['status','lines','cells','actors','epoch','rng']}))

if __name__=='__main__': main()

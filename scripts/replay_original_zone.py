#!/usr/bin/env python3
"""Validate Lean's heap against recorded original allocator calls (diagnostics only).

The call sequence and initial addresses are oracle inputs, not independently
generated Lean gameplay. WAD payloads and Lean-generated block headers supply
sampled bytes. Nothing from this replay is fed into the live renderer.
"""
import argparse
import json
from pathlib import Path
import struct
import subprocess

import original_demo_compare as oc

ROOT=oc.ROOT


def replay(trace, wad_path, cells, out, overreads=None):
    out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    wad=wad_path.read_bytes()
    _,count,directory=struct.unpack_from('<4sII',wad)
    lumps=[]
    for i in range(count):
        offset,size,name=struct.unpack_from('<II8s',wad,directory+i*16)
        lumps.append((name.rstrip(b'\0').decode(),wad[offset:offset+size]))
    fixture=json.loads(overreads.read_text()) if overreads else None
    if fixture:
        oc.require(oc.sha(wad)==fixture['wad_sha256'],'overread WAD mismatch')
        oc.require(oc.sha((trace.parent/'commands.txt').read_bytes())==fixture['commands_sha256'],'overread recording mismatch')
    sample_cases={c['tic']:c for c in fixture['cases']} if fixture else {}
    commands=[];expected=[];contexts=[];owner_pages=set();last_tag={}
    init=None;tic=0;allocations=0;sampled=0;calls=0;omitted=0;seen_tics=set()
    def append(command,want,context):
        commands.append(command);expected.append(want);contexts.append(context)
    def sample(t):
        nonlocal sampled
        if t not in sample_cases:return
        seen_tics.add(t)
        case=sample_cases[t]
        for p in case['samples']:
            append(f'sample {case["source_address"]} {p["source_offset"]} {p["row"]}',
                   f'ok {p["byte"]}',f'tic {t}, pixel {p["x"]},{p["y"]}')
            sampled+=1
    for line in trace.open():
        r=json.loads(line)
        if r.get('init'):
            if init:
                # Old diagnostic observer also sees a shared Z_CheckHeap return
                # at Z_Init's epilogue. An identical metadata row is not a reset.
                oc.require(r==init,'unexpected zone relocation/reinitialization')
                continue
            init=r
            append(f'unknown {r["base"]} {r["size"]}','ok 0','reserve unknown zone')
            append(f'zone {r["base"]} {r["size"]}','ok 0','initialize allocator')
            continue
        oc.require(init is not None,'allocator event precedes zone initialization')
        if r['tic']!=tic:
            sample(tic);tic=r['tic']
        calls+=1
        a,d,b=r['a'],r['d'],r['b']
        op=r['op']
        context=f'seq {r["seq"]}, tic {tic}, caller {r["caller"]:x}'
        if op==0x39690:
            if b and not init['base']<=b<init['base']+init['size']:
                page=b&~4095
                if page not in owner_pages:
                    append(f'unknown {page} 4096','ok 0',context)
                    owner_pages.add(page)
            append(f'alloc {a} {d} {b}',f'ok {r["result"]}',context)
            allocations+=1
            last_tag[r['result']]=d
            if r['caller']==0x38d41:
                oc.require(b>=cells and (b-cells)%4==0,'invalid WAD owner cell')
                index=(b-cells)//4
                if index<count:
                    name,data=lumps[index]
                    oc.require(len(data)==a,f'lump length mismatch: {name}')
                    path=out/f'lump-{index}.bin'
                    path.write_bytes(data)
                    append(f'load {r["result"]} {path}','ok 0',context)
                else:
                    oc.require(index==count and a==40014,'unrecognized external lump')
                    # The input demo is not a WAD texture and remains unknown.
        elif op==0x39600:
            append(f'free {a}','ok 0',context);last_tag.pop(a,None)
        elif op==0x399b0:
            if last_tag.get(a)==d:
                omitted+=1
            else:
                append(f'tag {a} {d}','ok 0',context);last_tag[a]=d
        elif op==0x39780:
            append(f'tags {a} {d}','ok 0',context)
            last_tag={ptr:tag for ptr,tag in last_tag.items() if not a<=tag<=d}
        elif op==0x39570:
            oc.require(a==init['base'],'clear targets another zone')
            append('clear','ok 0',context);last_tag={}
        else:raise ValueError(f'unknown allocator operation {op:x}')
    sample(tic)
    oc.require(seen_tics==set(sample_cases),'recording omitted a requested sample tic')
    path=out/'commands.txt';path.write_text('\n'.join(commands)+'\n')
    (out/'expectations.json').write_text(json.dumps(list(zip(contexts,expected)),indent=2)+'\n')
    proc=subprocess.run([str(ROOT/'.lake/build/bin/dos-memory-probe'),str(path)],capture_output=True,text=True,check=True)
    (out/'lean.log').write_text(proc.stdout)
    oc.require(not proc.stderr,proc.stderr)
    actual=proc.stdout.splitlines()
    oc.require(len(actual)==len(expected),'incomplete allocator replay')
    for i,(got,want) in enumerate(zip(actual,expected)):
        oc.require(got==want,f'{contexts[i]}: {commands[i]}: {got}, expected {want}')
    report={'status':'match','recorded_calls':calls,'allocations_matched':allocations,
            'redundant_same_tag_calls_omitted':omitted,'texture_overread_samples_matched':sampled,
            'initial_zone':init,'lump_cache_cells':cells,'trace_sha256':oc.sha(trace.read_bytes()),
            'wad_sha256':oc.sha(wad),'lean_executable_sha256':oc.sha((ROOT/'.lake/build/bin/dos-memory-probe').read_bytes()),
            'scope':'Recorded-call heap replay. Startup/runtime call ordering and initial addresses are supplied by DOS, not independently generated by Lean gameplay. Only initialized allocator/WAD bytes may be sampled; other RAM stays unknown.'}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--trace',type=Path,required=True)
    p.add_argument('--wad',type=Path,default=ROOT/'artifacts/doom-shareware-1.9/doom1.wad')
    p.add_argument('--lump-cells',type=lambda s:int(s,0),required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--overreads',type=Path)
    a=p.parse_args();replay(a.trace.resolve(),a.wad.resolve(),a.lump_cells,a.out.resolve(),a.overreads)

#!/usr/bin/env python3
"""Matched-state RGB frame comparison with pinned Chocolate DOOM (not DOS video).

One presentation after each demo prefix; 320x200, high detail, 320x168 world,
original WAD palette, no host gamma/scaling. Fuzz starts at phase zero.
Exit 0 means exact pixels; 1 means a visual difference; 2 means invalid evidence.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import struct
import sys
import zlib
import demo_compare as dc

ROOT=dc.ROOT


def read_ppm(path):
    parts=Path(path).read_bytes().split(b'\n',3)
    dc.require(len(parts)==4 and parts[:3]==[b'P6',b'320 200',b'255'] and len(parts[3])==320*200*3,
               'invalid 320x200 RGB frame')
    return parts[3]


def compare_pixels(reference,candidate):
    dc.require(len(reference)==len(candidate)==320*200*3,'incomplete pixels')
    differing=[reference[i:i+3]!=candidate[i:i+3] for i in range(0,len(reference),3)]
    def region(start,stop):
        count=sum(differing[start*320:stop*320]);total=(stop-start)*320
        return {'different_pixels':count,'pixels':total,'exact_fraction':(total-count)/total}
    return {'status':'different' if any(differing) else 'exact',
            'full':region(0,200),'world_and_weapon':region(0,168),'status_bar':region(168,200),
            'first_difference':next(({'x':i%320,'y':i//320,'reference':list(reference[3*i:3*i+3]),
                                     'lean':list(candidate[3*i:3*i+3])} for i,d in enumerate(differing) if d),None)}


def diff_ppm(reference,candidate):
    out=bytearray(b'P6\n320 200\n255\n')
    for i in range(0,len(reference),3):
        a,b=reference[i:i+3],candidate[i:i+3]
        out.extend([255,0,0] if a!=b else [sum(a)//6]*3)
    return bytes(out)


def png(pixels):
    dc.require(len(pixels)==320*200*3,'incomplete PNG pixels')
    def chunk(kind,data):
        return struct.pack('>I',len(data))+kind+data+struct.pack('>I',zlib.crc32(kind+data))
    rows=b''.join(b'\0'+pixels[y*960:(y+1)*960] for y in range(200))
    return (b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',320,200,8,2,0,0,0))
            +chunk(b'IDAT',zlib.compress(rows))+chunk(b'IEND',b''))


def gallery(reports):
    rows=[]
    for tick,report in reports.items():
        rows.append(f'<section><h2>Tic {tick} · {report["full"]["different_pixels"]:,} differing pixels</h2><div>')
        for name,label in [('reference','Chocolate DOOM'),('lean','Lean DOOM'),('difference','Exact differences (red)')]:
            rows.append(f'<figure><figcaption>{label}</figcaption><a href="{tick}/{name}.png"><img src="{tick}/{name}.png" alt="{label}, tic {tick}"></a></figure>')
        rows.append('</div></section>')
    return '''<!doctype html><meta charset="utf-8"><title>Lean DOOM rendering comparison</title>
<style>body{background:#111;color:#eee;font:16px system-ui;margin:32px;max-width:1300px}h1{font-size:24px}h2{font-size:17px;font-weight:500}p,figcaption{color:#aaa}section{margin:36px 0}section>div{display:flex;gap:16px}figure{margin:0;flex:1;min-width:0}img{width:100%;image-rendering:pixelated}figcaption{margin-bottom:8px}@media(max-width:700px){section>div{display:block}figure{margin-bottom:20px}}</style>
<h1>Same gameplay state, different renderers</h1>
<p>Raw 320×200 RGB. Gameplay traces match before comparison. Chocolate DOOM is the rendering reference here; this is not DOS video capture or a proof of pixel equivalence.</p>
'''+''.join(rows)


def run(args):
    commands=dc.decode_demo(Path(args.demo).read_bytes()) if args.demo else dc.scenario(args.scenario)
    dc.require(args.ticks and all(0<n<=len(commands) for n in args.ticks),'sample outside supplied demo')
    out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
    wad=ROOT/'artifacts/doom-shareware-1.9/doom1.wad'
    shareware=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    dc.require(dc.sha(wad.read_bytes())==shareware['wad_sha256'],'WAD hash mismatch')
    binary,identity=dc.build_reference(args.fetch,render_capture=True)
    with (out/'lean-build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','render-probe','trace-probe'],cwd=ROOT,stdout=log,stderr=log,check=True)
    reports={}
    for tick in args.ticks:
        p=out/str(tick);p.mkdir(exist_ok=True)
        prefix=commands[:tick];data=dc.encode_demo(prefix)
        (p/'input.lmp').write_bytes(data)
        (p/'commands.txt').write_text(''.join(' '.join(map(str,c))+'\n' for c in prefix))
        (p/'default.cfg').write_text('screenblocks 10\ndetaillevel 0\nusegamma 0\nshow_messages 1\n')
        (p/'chocolate.cfg').write_text('')
        env={**os.environ,'SDL_VIDEODRIVER':'dummy','SDL_AUDIODRIVER':'dummy',
             'LEANDOOM_TRACE':str(p/'reference.jsonl'),'LEANDOOM_TRACE_TICS':str(tick),
             'LEANDOOM_FRAME':str(p/'reference.ppm')}
        with (p/'reference.log').open('w') as log:
            subprocess.run([str(binary),'-iwad',str(wad),'-timedemo',str(p/'input.lmp'),'-gameversion','1.9',
                            '-nodraw','-nosound','-nojoy','-nomouse','-config',str(p/'default.cfg'),
                            '-extraconfig',str(p/'chocolate.cfg')],cwd=p,env=env,stdout=log,stderr=log,check=True,timeout=120)
        with (p/'lean.jsonl').open('w') as stream:
            subprocess.run([str(ROOT/'.lake/build/bin/trace-probe'),'E1M1',str(wad),str(p/'commands.txt')],
                           stdout=stream,check=True,timeout=120)
        reference=dc.read_records(p/'reference.jsonl');lean=dc.read_records(p/'lean.jsonl')
        dc.require(len(reference)==len(lean)==tick+1,'incomplete tick capture')
        dc.require([r['command'] for r in reference[1:]]==prefix,'reference input mismatch')
        gameplay=dc.compare(reference,lean)
        (p/'gameplay.json').write_text(json.dumps(gameplay,indent=2)+'\n')
        dc.require(gameplay['status']=='match','gameplay divergence prevents matched-state render comparison')
        subprocess.run([str(ROOT/'.lake/build/bin/render-probe'),str(wad),str(p/'commands.txt'),
                        str(p/'lean.ppm'),str(p/'render-state.json')],check=True,timeout=120)
        dc.require(json.loads((p/'render-state.json').read_text())==lean[-1]['state'],'renderer replay state differs')
        if args.repeat:
            repeat_env={**env,'LEANDOOM_TRACE':str(p/'reference-repeat.jsonl'),
                        'LEANDOOM_FRAME':str(p/'reference-repeat.ppm')}
            with (p/'reference-repeat.log').open('w') as log:
                subprocess.run([str(binary),'-iwad',str(wad),'-timedemo',str(p/'input.lmp'),'-gameversion','1.9',
                                '-nodraw','-nosound','-nojoy','-nomouse','-config',str(p/'default.cfg'),
                                '-extraconfig',str(p/'chocolate.cfg')],cwd=p,env=repeat_env,stdout=log,stderr=log,check=True,timeout=120)
            subprocess.run([str(ROOT/'.lake/build/bin/render-probe'),str(wad),str(p/'commands.txt'),
                            str(p/'lean-repeat.ppm'),str(p/'render-repeat-state.json')],check=True,timeout=120)
            for first,second in [('reference.ppm','reference-repeat.ppm'),('reference.jsonl','reference-repeat.jsonl'),
                                 ('lean.ppm','lean-repeat.ppm'),('render-state.json','render-repeat-state.json')]:
                dc.require((p/first).read_bytes()==(p/second).read_bytes(),f'nonrepeatable capture: {first}')
        a,b=read_ppm(p/'reference.ppm'),read_ppm(p/'lean.ppm')
        report=compare_pixels(a,b)
        report.update(tick=tick,gameplay='match',repeatability_checked=args.repeat,input_sha256=dc.sha(data),
                      reference_frame_sha256=dc.sha((p/'reference.ppm').read_bytes()),
                      lean_frame_sha256=dc.sha((p/'lean.ppm').read_bytes()),
                      reference_trace_sha256=dc.sha((p/'reference.jsonl').read_bytes()),
                      lean_trace_sha256=dc.sha((p/'lean.jsonl').read_bytes()))
        (p/'difference.ppm').write_bytes(diff_ppm(a,b));(p/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        for name in ['reference','lean','difference']:
            (p/f'{name}.png').write_bytes(png(read_ppm(p/f'{name}.ppm')))
        reports[str(tick)]=report
        print(f"tic {tick}: {report['full']['different_pixels']} / 64000 pixels differ; gameplay matches",flush=True)
    result={'oracle':'Pinned Chocolate DOOM renderer; not original DOS video capture',
            'reference':identity,'wad_sha256':shareware['wad_sha256'],
            'lean_executable_sha256':dc.sha((ROOT/'.lake/build/bin/render-probe').read_bytes()),
            'comparison_script_sha256':dc.sha(Path(__file__).read_bytes()),
            'presentation':'one presentation after each prefix; high detail; screenblocks 10; raw WAD palette; no gamma or scaling',
            'frames':reports}
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'index.html').write_text(gallery(reports))
    return 1 if any(r['status']!='exact' for r in reports.values()) else 0


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--demo');p.add_argument('--scenario',choices=dc.SCENARIOS,default='e1m1-exit')
    p.add_argument('--ticks',nargs='+',type=int,default=[1,777,1242,1881])
    p.add_argument('--fetch',action='store_true');p.add_argument('--repeat',action='store_true')
    p.add_argument('--out',default='artifacts/render-comparison')
    try:return run(p.parse_args())
    except (ValueError,OSError,subprocess.SubprocessError) as e:
        print(f'render comparison error: {e}',file=sys.stderr);return 2

if __name__=='__main__':sys.exit(main())

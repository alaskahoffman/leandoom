#!/usr/bin/env python3
"""Original-format demo playback, pinned reference traces, and first divergence.

Exit codes: 0 = selected trace fields match; 1 = behavioral divergence;
2 = invalid/unsupported input, incomplete trace, or tooling failure. No proof claim.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
SPEC = json.loads((ROOT/'tests/reference/tick-trace.json').read_text())
SCHEMA = SPEC['schema']
HEADER = bytes([109,2,1,1,0,0,0,0,0,1,0,0,0])
PLAYER_FIELDS = 'x y z momx momy momz angle floor ceiling viewZ viewHeight viewDelta bob health armor armorType readyWeapon secrets'.split()
BRAIN_FIELDS = 'state tics angle movedir movecount reaction threshold lastlook target behaviorFlags x y z momx momy momz health'.split()
IMPACT_FIELDS = 'x y z momz floor ceiling state tics lastlook'.split()
PROJECTILE_FIELDS = 'x y z momx momy momz angle floor ceiling state tics source lastlook missile'.split()
SCENARIOS = ['idle','movement','combat','moving-combat','enemy-encounter','shotgun-secret','e1m1-exit','sky-window']
WEAPON_FIELDS = 'state tics x y flashState flashTics refire extraLight'.split()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def decode_demo(data):
    require(len(data) >= 14, 'truncated demo header/end marker')
    require(data[0] == 109, 'unsupported demo version: require vanilla 1.9 (109), not longtics')
    require(data[1:13] == HEADER[1:13], 'unsupported demo profile: require E1M1, Hurt Me Plenty, player 1 only, default gameplay flags')
    commands, offset = [], 13
    while offset < len(data):
        if data[offset] == 0x80:
            require(not any(data[offset+1:]), 'nonzero trailing data after demo end marker')
            require(commands, 'empty demo: at least one command required')
            return commands
        require(offset+4 <= len(data), f'truncated command at byte {offset}')
        f,s,a,b = struct.unpack_from('<bbbB',data,offset)
        require(b & 0xc0 == 0, f'unsupported special/reserved buttons at tic {len(commands)}')
        require(not b & 4 or (b >> 3) & 7 <= 2, f'unsupported weapon selection at tic {len(commands)}')
        commands.append([f,s,a*256,b])
        require(len(commands) <= 10000, 'demo exceeds initial 10000-tic harness limit')
        offset += 4
    raise ValueError('missing demo end marker')


def encode_demo(commands):
    data = bytearray(HEADER)
    for f,s,a,b in commands:
        require(a % 256 == 0, 'vanilla demo turns must be multiples of 256')
        data.extend(struct.pack('<bbbB',f,s,a//256,b))
    data.append(0x80)
    decode_demo(data)
    return bytes(data)


def scenario(name):
    if name == 'sky-window':
        # Normal spawn to the western armor-room window, for renderer checks.
        segments = [(1,0,0,16384,0),(50,50,0,0,0),(35,0,0,0,0),
                    (17,0,50,0,0),(20,0,0,0,0),(40,50,0,0,0),(20,0,0,0,0)]
        return [list(cmd) for ticks,*cmd in segments for _ in range(ticks)]
    if name == 'e1m1-exit':
        # Leave the secret, kill the last imp, let the door crush its corpse,
        # and use the exit switch. Stop before G_DoCompleted/intermission.
        segments = [
            (1, 0, 0, 16384, 0),
            (14, 50, 0, 0, 0),
            (20, 0, 0, 0, 0),
            (1, 0, 0, 16384, 0),
            (24, 50, 0, 0, 0),
            (20, 0, 0, 0, 0),
            (1, 0, 0, 16384, 0),
            (24, 50, 0, 0, 0),
            (20, 0, 0, 0, 0),
            (1, 0, 0, 16384, 0),
            (23, 50, 0, 0, 1),
            (20, 0, 0, 0, 1),
            (1, 0, 0, 0, 2),
            (45, 0, 0, 0, 1),
            (20, 50, 0, 0, 1),
            (100, 0, 0, 0, 1),
            (24, 50, 0, 0, 0),
            (20, 0, 0, 0, 0),
            (1, 0, 0, 0, 2),
            (45, 0, 0, 0, 0),
            (12, 50, 0, 0, 0),
            (20, 0, 0, 0, 0),
            (1, 0, 0, -16384, 0),
            (5, 25, 25, 0, 0),
            (20, 0, 0, 0, 0),
            (1, 0, 0, 0, 2),
        ]
        return scenario('shotgun-secret') + [list(cmd) for ticks,*cmd in segments for _ in range(ticks)]
    if name == 'shotgun-secret':
        # Ordinary inputs from normal spawn; no relocation, cheats, or patched
        # WAD. Keep the first encounter as an exact prefix of this longer route.
        segments = [
            # Collect dropped ammo, skirt the stairs, fight along the passage.
            (35,50,0,0,0),(15,0,0,0,0),(15,-50,0,0,0),(20,0,0,0,0),
            (8,0,50,0,0),(20,0,0,0,0),(36,50,0,0,0),(20,0,0,0,0),
            (1,0,0,-8192,0),(16,50,0,0,1),(100,0,0,0,1),
            (1,0,0,25600,0),(80,0,0,0,1),(1,0,0,31744,0),
            (28,50,0,0,0),(35,0,0,0,0),(90,0,0,0,1),(30,50,0,0,1),
            (30,0,0,0,0),
            # Imp combat, slime contact, retreat and finish the imp.
            (1,0,0,18944,0),(100,0,0,0,1),(20,50,0,0,1),(30,0,0,0,0),
            (15,-50,0,0,0),(20,0,0,0,0),(150,0,0,0,1),
            # Second door, floor-lowering trigger, return past the zombieman.
            (1,0,0,-18944,0),(22,50,0,0,0),(20,0,0,0,0),
            (1,0,0,0,2),(45,0,0,0,0),(22,50,0,0,0),(20,0,0,0,0),
            (1,0,0,0,2),(45,0,0,0,0),(16,50,0,0,0),(15,0,0,0,0),
            (1,0,0,-32768,0),(40,50,0,0,1),(20,0,0,0,1),
            # Cross to the lowered platform and discover the shotgun secret.
            (10,0,0,0,0),(1,0,0,-13824,0),(23,50,0,0,0),(20,0,0,0,0),
            (1,0,0,-18944,0),(19,50,0,0,0),(20,0,0,0,0),
            (1,0,0,-16384,0),(10,50,0,0,0),(20,0,0,0,0),
            (1,0,0,16384,0),(8,50,0,0,0),(40,0,0,0,0),
            # Let the pickup auto-switch, then fire three shotgun blasts.
            (80,0,0,0,1),
        ]
        return scenario('enemy-encounter') + [list(cmd) for ticks,*cmd in segments for _ in range(ticks)]
    if name == 'idle': return [[0,0,0,0]]*70
    if name == 'movement':
        return [[0,0,0,0]]*35 + [[25,0,0,0]]*35 + [[0,0,512,0]]*16 + [[17,-9,-768,0]]*20 + [[0,0,0,0]]*35
    if name == 'moving-combat':
        return [[0,0,0,0]]*40 + [[17,-9,-256,1]]*20 + [[-17,9,256,1]]*20 + [[0,0,0,1]]*30 + [[0,0,0,0]]*35
    if name == 'enemy-encounter':
        return ([[0,0,0,0]]*40 + [[50,0,0,0]]*40 + [[0,0,0,0]]*35
                + [[0,50,0,0]]*14 + [[0,0,0,0]]*35 + [[50,0,0,0]]*35
                + [[0,0,0,0]]*35 + [[0,0,-16384,0]] + [[50,0,0,0]]*40
                + [[0,0,0,2]] + [[0,0,0,0]]*45 + [[50,0,0,0]]*30
                + [[0,0,0,0]]*70 + [[0,0,0,1]]*100)
    require(name == 'combat' , 'unknown scenario')
    return [[0,0,0,0]]*40 + [[0,0,0,1]]*90 + [[0,0,0,2]]*5 + [[0,0,0,0]]*35


def replace_once(source, old, new):
    require(source.count(old) == 1, f'upstream instrumentation anchor changed: {old!r}')
    return source.replace(old,new)


def build_reference(fetch=False, render_capture=False):
    archive = ROOT/'artifacts/reference/chocolate-doom-3.1.1-full.tar.gz'
    if not archive.exists():
        require(fetch, 'reference archive missing; rerun with --fetch (network only for pinned source)')
        archive.parent.mkdir(parents=True,exist_ok=True)
        url = f"https://codeload.github.com/chocolate-doom/chocolate-doom/tar.gz/{SPEC['commit']}"
        data = urllib.request.urlopen(url,timeout=60).read()
        require(sha(data) == SPEC['archive_sha256'], 'reference archive hash mismatch')
        archive.write_bytes(data)
    require(sha(archive.read_bytes()) == SPEC['archive_sha256'], 'reference archive hash mismatch')
    work = ROOT/('artifacts/render-reference' if render_capture else 'artifacts/tick-reference')
    source = work/f"chocolate-doom-{SPEC['commit']}"
    observer = (ROOT/'tests/reference/tick_trace.inc').read_text()
    frame_observer = (ROOT/'tests/reference/frame_capture.inc').read_text() if render_capture else ''
    if render_capture:
        observer = frame_observer + '\n' + replace_once(observer,
            '        if (fclose(ltrace_file))', '        LRenderCapture();\n        if (fclose(ltrace_file))')
    # Fresh extraction makes instrumentation idempotent and discards accidental
    # edits to cached source. The archive and observer remain the source of truth.
    work.mkdir(parents=True,exist_ok=True)
    if source.exists(): shutil.rmtree(source)
    with tarfile.open(archive) as tar:
        tar.extractall(work,filter='data')
    manifest = json.loads((ROOT/'tests/reference/manifest.json').read_text())
    for name,digest in manifest['files'].items():
        require(sha((source/name).read_bytes()) == digest, f'reference file hash mismatch: {name}')
    doom = source/'src/doom'
    (doom/'tick_trace.inc').write_text(observer)
    p = doom/'g_game.c'
    text = replace_once(p.read_text(),'void G_Ticker (void)', '#include "tick_trace.inc"\n\nvoid G_Ticker (void)')
    text = replace_once(text,'\tP_Ticker ();', '\tLTraceBefore();\n\tP_Ticker ();')
    text = replace_once(text,'\tHU_Ticker ();', '\tHU_Ticker ();\n\tLTraceAfter();')
    p.write_text(text)
    p = doom/'p_setup.c'
    text = replace_once(p.read_text(),'\tP_SpawnMapThing(&spawnthing);', '\tLTraceMapIndex = i;\n\tP_SpawnMapThing(&spawnthing);\n\tLTraceMapIndex = -1;')
    p.write_text('extern int LTraceMapIndex;\n'+text)
    p = doom/'p_mobj.c'
    text = p.read_text()
    # Function-local anchor avoids changing the unrelated return in missile code.
    text = replace_once(text,'    P_AddThinker (&mobj->thinker);', '    P_AddThinker (&mobj->thinker);\n    LTraceSpawn(mobj);')
    text = replace_once(text,'void P_RemoveMobj (mobj_t* mobj)\n{','void P_RemoveMobj (mobj_t* mobj)\n{\n    LTraceRemove(mobj);')
    text = replace_once(text,'#include "p_local.h"', '#include "p_local.h"\nvoid LTraceSpawn(mobj_t *mo);\nvoid LTraceRemove(mobj_t *mo);')
    p.write_text(text)
    if render_capture:
        p = source/'src/i_video.c'
        text = replace_once(p.read_text(),'void I_SetPalette (byte *doompalette)\n{',
            'unsigned char LRenderPalette[768];\nvoid I_SetPalette (byte *doompalette)\n{\n    memcpy(LRenderPalette, doompalette, 768);')
        p.write_text(text)
    build = work/'build'
    with (work/'build.log').open('w') as log:
        subprocess.run(['cmake','-S',str(source),'-B',str(build),'-DENABLE_SDL2_MIXER=OFF',
                        '-DENABLE_SDL2_NET=OFF','-DCMAKE_BUILD_TYPE=Release','-DCMAKE_C_FLAGS=-fwrapv',
                        '-DCMAKE_POLICY_VERSION_MINIMUM=3.5'],stdout=log,stderr=subprocess.STDOUT,check=True)
        subprocess.run(['cmake','--build',str(build),'--target','chocolate-doom','-j','4'],
                       stdout=log,stderr=subprocess.STDOUT,check=True)
    binary=build/'src/chocolate-doom'
    require(binary.exists(),'reference binary missing after build')
    return binary, {'commit':SPEC['commit'],'archive_sha256':SPEC['archive_sha256'],
                    'observer_sha256':sha(observer.encode()),'executable_sha256':sha(binary.read_bytes()),
                    'instrumenter_sha256':sha(Path(__file__).read_bytes())}


def integer_object(value, fields, label):
    require(type(value) is dict and set(value)==set(fields),f'{label}: field schema mismatch')
    require(all(type(v) is int for v in value.values()),f'{label}: expected raw integers')


def validate_state(state):
    require(type(state) is dict and set(state)==set(SPEC['compared']), 'trace state schema mismatch')
    require(type(state['levelTime']) is int and type(state['exitRequested']) is bool,'invalid time/exit fields')
    integer_object(state['rng'],['play','misc'],'rng')
    require(all(0<=v<=255 for v in state['rng'].values()),'invalid RNG indices')
    player=state['player']
    require(type(player) is dict and 'ammo' in player and 'pendingWeapon' in player,'missing player/ammo/pendingWeapon')
    integer_object({k:v for k,v in player.items() if k not in ['ammo','pendingWeapon']},PLAYER_FIELDS,'player')
    require(player['pendingWeapon'] is None or (type(player['pendingWeapon']) is int and 0<=player['pendingWeapon']<=8),'invalid pending weapon')
    require(type(player['ammo']) is list and len(player['ammo'])==4 and all(type(v) is int for v in player['ammo']),'invalid ammo')
    integer_object(state['weapon'],WEAPON_FIELDS,'weapon')
    require(type(state['sectors']) is list and state['sectors'],'missing sectors')
    for sector in state['sectors']: integer_object(sector,['floor','ceiling','light','special'],'sector')
    for key in ['lineSpecials','sideOffsets']:
        require(type(state[key]) is list and state[key] and all(type(v) is int for v in state[key]),f'invalid {key}')
    require(type(state['impacts']) is list,'invalid impact array')
    for effect in state['impacts']: integer_object(effect,IMPACT_FIELDS,'impact')
    validate_projectiles(state['projectiles'])
    require(type(state['enemyBrains']) is dict,'invalid enemy brains')
    for key,value in state['enemyBrains'].items():
        require(key.isascii() and key.isdigit() and str(int(key))==key,'invalid enemy identity')
        integer_object(value,BRAIN_FIELDS,'enemy brain')
    require(type(state['actors']) is dict,'invalid actor mapping')
    for key,value in state['actors'].items():
        require(key.isascii() and key.isdigit() and str(int(key))==key,'invalid THINGS identity')
        integer_object(value,['kind','x','y','z','health'],'actor')


def validate_projectiles(shots):
    require(type(shots) is list,'invalid projectile array')
    for shot in shots:
        integer_object(shot,PROJECTILE_FIELDS,'projectile')
        for key,value in shot.items():
            require(0<=value<2**32 if key=='angle' else -2**31<=value<2**31,'projectile field outside range')
        require(97<=shot['state']<=101 and 0<=shot['lastlook']<4 and shot['missile'] in [0,1],
                'invalid imp fireball state/flags')
        require(shot['source']>=-1,'invalid projectile source')


def read_records(path):
    records=[]
    with Path(path).open() as stream:
        for line in stream:
            require(line.strip(), 'blank trace record')
            record=json.loads(line)
            require(type(record) is dict and type(record.get('tick')) is int and record['tick']==len(records), 'trace tick sequence must start at zero and be contiguous')
            validate_state(record.get('state'))
            require('command' in record, 'missing trace command')
            if not records: require(record['command'] is None,'initial record must have null command')
            else:
                require(type(record['command']) is list and len(record['command'])==4 and all(type(v) is int for v in record['command']), 'invalid trace command')
                encode_demo([record['command']])
            records.append(record)
    require(len(records)>1,'empty/incomplete trace: need initialization and at least one tick')
    require(not any(r['state']['exitRequested'] for r in records[:-1]),'intermission beyond exit request unsupported')
    return records


def differences(a,b,path='state'):
    if type(a) is not type(b):
        yield {'field':path,'reference':a,'lean':b}; return
    if isinstance(a,dict):
        for key in sorted(a.keys() | b.keys()):
            p=f'{path}.{key}'
            if key not in a or key not in b:
                yield {'field':p,'reference':a.get(key),'lean':b.get(key),'missing':'reference' if key not in a else 'lean'}
            else: yield from differences(a[key],b[key],p)
    elif isinstance(a,list):
        if len(a)!=len(b): yield {'field':path+'.length','reference':len(a),'lean':len(b)}
        for i,(x,y) in enumerate(zip(a,b)): yield from differences(x,y,f'{path}[{i}]')
    elif a!=b: yield {'field':path,'reference':a,'lean':b}


def compare(reference,lean):
    require(len(reference)==len(lean),f'incomplete traces: reference {len(reference)} records, Lean {len(lean)}')
    # Validate the entire command stream before reporting behavioral mismatches.
    for r,l in zip(reference,lean):
        require(r['tick']==l['tick'] and r['command']==l['command'],f'input/boundary mismatch at tick {r["tick"]}')
    first=None
    groups={}
    fields={}
    for r,l in zip(reference,lean):
        diffs=list(differences(r['state'],l['state']))
        if diffs and first is None:
            first={'tick':r['tick'],'phase':'initialization' if r['tick']==0 else 'after-tick',
                   'command':r['command'],'differences':diffs[:40], 'difference_count':len(diffs),
                   'previous_matching_tick':r['tick']-1 if r['tick'] else None}
        for diff in diffs:
            if diff['field'] not in fields: fields[diff['field']]={'tick':r['tick'],**diff}
            group=diff['field'].split('.')[1].split('[')[0]
            if group not in groups: groups[group]={'tick':r['tick'],**diff}
    return {'schema':SCHEMA,'status':'diverged' if first else 'match',
            'ticks_compared':len(reference)-1,'initial_state_compared':True,
            'first_divergence':first,'first_by_subsystem':groups,'first_by_field':fields,'coverage':SPEC['compared'],
            'excluded':SPEC['excluded'],'oracle':SPEC['oracle'],
            'provenance_verified':False}


def run(args):
    out=Path(args.out).resolve(); out.mkdir(parents=True,exist_ok=True)
    for name in ['report.json','reference.jsonl','lean.jsonl','provenance.json']:
        (out/name).unlink(missing_ok=True)
    original=Path(args.demo).read_bytes() if args.demo else encode_demo(scenario(args.scenario))
    commands=decode_demo(original)
    require(0<args.ticks<=10000,'--ticks must be 1..10000')
    commands=commands[:args.ticks]
    data=encode_demo(commands)
    (out/'input.lmp').write_bytes(data)
    (out/'commands.txt').write_text(''.join(' '.join(map(str,c))+'\n' for c in commands))
    wad=ROOT/'artifacts/doom-shareware-1.9/doom1.wad'
    shareware=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    require(sha(wad.read_bytes())==shareware['wad_sha256'],'shareware WAD hash mismatch')
    binary,identity=build_reference(args.fetch)
    with (out/'lean-build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','trace-probe'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    env={**os.environ,'SDL_VIDEODRIVER':'dummy','SDL_AUDIODRIVER':'dummy',
         'LEANDOOM_TRACE':str(out/'reference.jsonl'),'LEANDOOM_TRACE_TICS':str(len(commands))}
    for name in ['default.cfg','chocolate.cfg']: (out/name).write_text('')
    with (out/'reference.log').open('w') as log:
        subprocess.run([str(binary),'-iwad',str(wad),'-timedemo',str(out/'input.lmp'),
                        '-gameversion','1.9','-nodraw','-nosound','-nojoy','-nomouse','-config',str(out/'default.cfg'),
                        '-extraconfig',str(out/'chocolate.cfg')],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120)
    with (out/'lean.jsonl').open('w') as stream, (out/'lean.log').open('w') as log:
        subprocess.run([str(ROOT/'.lake/build/bin/trace-probe'),'E1M1',str(wad),str(out/'commands.txt')],
                       cwd=ROOT,stdout=stream,stderr=log,check=True,timeout=120)
    ref=read_records(out/'reference.jsonl'); lean=read_records(out/'lean.jsonl')
    require(len(ref)==len(commands)+1 and len(lean)==len(commands)+1,'trace did not capture all requested commands')
    require([r['command'] for r in ref[1:]]==commands,'reference did not execute the supplied demo commands')
    provenance={'schema':SCHEMA,'profile':SPEC['profile'],'boundary':SPEC['boundary'],
                'reference':identity,'wad_sha256':shareware['wad_sha256'],
                'source_demo_sha256':sha(original),'executed_demo_sha256':sha(data),
                'lean_executable_sha256':sha((ROOT/'.lake/build/bin/trace-probe').read_bytes()),
                'reference_trace_sha256':sha((out/'reference.jsonl').read_bytes()),
                'lean_trace_sha256':sha((out/'lean.jsonl').read_bytes())}
    (out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    report=compare(ref,lean)
    report['provenance_verified']=True
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    subs=parser.add_subparsers(dest='action',required=True)
    p=subs.add_parser('run'); p.add_argument('--demo'); p.add_argument('--scenario',choices=SCENARIOS,default='movement')
    p.add_argument('--ticks',type=int,default=200); p.add_argument('--fetch',action='store_true')
    p.add_argument('--out',default=str(ROOT/'artifacts/demo-comparison'))
    p=subs.add_parser('compare'); p.add_argument('reference'); p.add_argument('lean'); p.add_argument('--out')
    p=subs.add_parser('make-demo'); p.add_argument('output'); p.add_argument('--scenario',choices=SCENARIOS,default='movement')
    args=parser.parse_args()
    if args.action=='make-demo':
        Path(args.output).write_bytes(encode_demo(scenario(args.scenario))); return 0
    if args.action=='run': report=run(args)
    else:
        report=compare(read_records(args.reference),read_records(args.lean))
        if args.out: Path(args.out).write_text(json.dumps(report,indent=2)+'\n')
    if report['first_divergence']:
        d=report['first_divergence']; print(f"DIVERGENCE at tick {d['tick']} ({d['phase']}); {d['difference_count']} differing fields")
        for v in d['differences'][:10]: print(f"  {v['field']}: reference={v['reference']!r}; Lean={v['lean']!r}")
        print('First difference by subsystem:')
        for name,v in report['first_by_subsystem'].items():
            print(f"  {name}: tick {v['tick']}, {v['field']}: {v['reference']!r} vs {v['lean']!r}")
    else: print(f"MATCH: initialization + {report['ticks_compared']} tics (declared fields only)")
    print(f"Oracle: {report['oracle']}")
    if args.out: print(f"Report: {Path(args.out)/'report.json' if args.action=='run' else args.out}")
    return 1 if report['first_divergence'] else 0


if __name__=='__main__':
    try: sys.exit(main())
    except (ValueError,OSError,subprocess.SubprocessError,tarfile.TarError,struct.error) as error:
        print(f'comparison harness error: {error}',file=sys.stderr); sys.exit(2)

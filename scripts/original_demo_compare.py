#!/usr/bin/env python3
"""Compare selected per-tic state against unchanged DOS DOOM.EXE in DOSBox-X.

Exit 0: declared fields match; 1: divergence; 2: incomplete/invalid evidence.
Chocolate Doom remains a separate diagnostic candidate, not the final oracle.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tarfile
import urllib.request

import demo_compare as dc
import verify_original_mul as mul
from verify_original_arithmetic import fixups

ROOT = dc.ROOT
SPEC = json.loads((ROOT/'tests/reference/original-tick.json').read_text())
PROFILE = json.loads((ROOT/'tests/reference/original-mul.json').read_text())
SHAREWARE = json.loads((ROOT/'tests/reference/shareware.json').read_text())
FIELDS = tuple(SPEC['mobj_offsets'])
PLAYER_SCALARS = FIELDS + ('health','armor','armorType','readyWeapon','secrets')
require, sha = dc.require, dc.sha
CONFIGURE = ['--enable-sdl2', '--disable-sdlnet', '--disable-libslirp',
             '--disable-libfluidsynth', '--disable-avcodec', '--disable-mt32',
             '--disable-printer', '--disable-freetype', '--disable-opengl',
             '--disable-xbrz', '--disable-dynamic-core', '--disable-debug',
             '--disable-screenshots', '--disable-gamelink', 'CFLAGS=-O2', 'CXXFLAGS=-O2']


def verify_image(binary):
    mul.checked_hash(binary, PROFILE['exe_sha256'], 'DOOM.EXE')
    code, _, relocations, _ = mul.inspect_image(binary, PROFILE)
    before, after = int(SPEC['before'],16), int(SPEC['after'],16)
    signature = bytes.fromhex(SPEC['signature_hex'])
    require(after == before+20 and len(signature) == 22, 'invalid boundary profile')
    require(code[before:before+22] == signature and code.count(signature) == 1,
            'tick boundary is not the unique expected instruction sequence')
    require(not any(max(before,p)<min(before+22,p+n) for p,n in relocations),
            'tick boundary overlaps loader relocation')
    actual = fixups(binary,range((len(code)+4095)//4096))
    for operand,target in SPEC['data_operands'].items():
        p,t = int(operand,16),int(target,16)
        require(struct.unpack_from('<I',code,p)[0] == t and (p,3,t) in actual,
                f'data-object relocation mismatch at {operand}')
    for operand,target in SPEC.get('code_operands',{}).items():
        p,t=int(operand,16),int(target,16)
        require(struct.unpack_from('<I',code,p)[0]==t and (p,1,t) in actual,
                f'code-object relocation mismatch at {operand}')
    for name,evidence in SPEC['code_evidence'].items():
        p = int(evidence['code_offset'],16); raw = bytes.fromhex(evidence['hex'])
        require(code[p:p+len(raw)] == raw, f'instruction evidence changed: {name}')
    for group in ['enemy','player','psprite','projectile']:
        require(set(SPEC[group+'_offsets'])==set(SPEC[group+'_offset_evidence']),f'{group} offset evidence incomplete')
        for name,evidence in SPEC[group+'_offset_evidence'].items():
            pc=int(evidence['code_offset'],16); raw=bytes.fromhex(evidence['hex'])
            require(code[pc:pc+len(raw)]==raw,f'{group} field instruction changed: {name}')
            start=evidence['displacement_offset']; width=evidence['displacement_bytes']
            require(0<=start<=len(raw) and width in [0,1,4] and start+width<=len(raw),'invalid displacement evidence')
            require(int.from_bytes(raw[start:start+width],'little')==SPEC[group+'_offsets'][name],f'{group} field offset mismatch: {name}')
    require(SPEC['player_layout']=={'ammo_count':4,'ammo_stride':4,'psprite_count':2,
            'psprite_stride':16,'no_pending_weapon':10,'mobj_player_offset':132,'weapon_count':9},'unsupported player layout')
    for name,evidence in SPEC['layout_value_evidence'].items():
        pc=int(evidence['code_offset'],16);raw=bytes.fromhex(evidence['hex'])
        start=evidence['value_offset'];width=evidence['value_bytes']
        require(code[pc:pc+len(raw)]==raw and
                int.from_bytes(raw[start:start+width],'little')==SPEC['player_layout'][name],
                f'player layout instruction mismatch: {name}')
    require(SPEC['enemy_state_table']=={'data_offset':'0x15a28','stride':28,'count':967},'unsupported enemy state table')
    require(len(SPEC['enemy_profile'])==6,'unsupported enemy roster')
    require(SPEC['projectile_layout']=={'type':31,'missile_mask':65536,'first_state':97,'last_state':101},
            'unsupported projectile layout')
    return binary


def original_image():
    archive = ROOT/'artifacts/doom-shareware-1.9/doom19s.zip'
    return verify_image(mul.extract(archive,SHAREWARE,PROFILE))


def build_emulator(fetch=False, rebuild=False):
    """Cache only a hash-checked binary built from a fresh pinned extraction.

    Cached source edits are never rebuilt incrementally. Changing the observer,
    builder, profile or binary invalidates the cache and triggers fresh extraction.
    This is local provenance bookkeeping, not a signed build attestation.
    """
    emulator = SPEC['emulator']
    archive = ROOT/'artifacts/reference/dosbox-x-e013b8bf.tar.gz'
    if not archive.exists():
        require(fetch, 'DOSBox-X source archive missing; use --fetch')
        data = urllib.request.urlopen(f"https://codeload.github.com/joncampbell123/dosbox-x/tar.gz/{emulator['commit']}",timeout=120).read()
        require(sha(data)==emulator['archive_sha256'],'DOSBox-X archive hash mismatch')
        archive.parent.mkdir(parents=True,exist_ok=True); archive.write_bytes(data)
    require(sha(archive.read_bytes())==emulator['archive_sha256'],'DOSBox-X archive hash mismatch')
    work = ROOT/'artifacts/original-reference'; work.mkdir(parents=True,exist_ok=True)
    source = work/f"dosbox-x-{emulator['commit']}"
    binary = source/'src/dosbox-x'
    observer = (ROOT/'tests/reference/dosbox_tick_trace.h').read_bytes()
    identity = {**emulator, 'observer_sha256':sha(observer),
                'builder_sha256':sha(Path(__file__).read_bytes()),
                'profile_sha256':sha((ROOT/'tests/reference/original-tick.json').read_bytes()),
                'configure':CONFIGURE}
    cache = work/'build.json'
    if not rebuild and cache.exists() and binary.exists():
        saved = json.loads(cache.read_text())
        if saved.get('inputs')==identity and saved.get('executable_sha256')==sha(binary.read_bytes()):
            return binary,saved
    cache.unlink(missing_ok=True)
    if source.exists(): shutil.rmtree(source)
    with tarfile.open(archive) as tar: tar.extractall(work,filter='data')
    core = source/'src/cpu/core_normal.cpp'
    text = dc.replace_once(core.read_text(),'Bits CPU_Core_Normal_Run(void) {',
                           '#include "dosbox_tick_trace.h"\n\nBits CPU_Core_Normal_Run(void) {')
    require('\t\tLOADIP;' in text,'normal-core instruction boundary missing')
    # The first LOADIP belongs to CPU_Core_Normal_Run (not its trap wrapper).
    text = text.replace('\t\tLOADIP;','\t\tLOADIP;\n        LeanDoomObserve(core.cseip);',1)
    profile = 'static const int ld_enemy_ids[] = {'+','.join(str(e['id']) for e in SPEC['enemy_profile'])+'};\n'
    profile += 'static const int ld_enemy_spawns[][5] = {'+','.join('{'+','.join(map(str,e['spawn']))+'}' for e in SPEC['enemy_profile'])+'};\n'
    profile += 'static const unsigned ld_enemy_types[] = {'+','.join(str(e['type']) for e in SPEC['enemy_profile'])+'};\n'
    for name,offset in SPEC['enemy_offsets'].items(): profile += f'static const unsigned ld_{name} = {offset};\n'
    for group in ['player','psprite','projectile']:
        for name,offset in SPEC[group+'_offsets'].items(): profile += f'static const unsigned ld_{group}_{name} = {offset};\n'
    for name,value in SPEC['player_layout'].items(): profile += f'static const unsigned ld_{name} = {value};\n'
    for name,value in SPEC['projectile_layout'].items(): profile += f'static const unsigned ld_shot_{name} = {value};\n'
    core.write_text(text)
    (core.parent/'dosbox_tick_trace.h').write_text(observer.decode().replace('/* ENEMY_PROFILE */',profile))
    with (work/'build.log').open('w') as log:
        for command in [['./autogen.sh'], ['./configure',*CONFIGURE], ['make','-j4']]:
            subprocess.run(command,cwd=source,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
    require(binary.exists(),'DOSBox-X executable missing after build')
    saved = {'inputs':identity,'executable_sha256':sha(binary.read_bytes())}
    cache.write_text(json.dumps(saved,indent=2)+'\n')
    return binary,saved


def validate_records(records, commands):
    dc.encode_demo(commands)
    require(len(records)==len(commands)+1,'original trace did not capture every requested command')
    for tick,row in enumerate(records):
        require(type(row) is dict and set(row)=={'tick','command','state'},'invalid original record schema')
        require(type(row['tick']) is int and row['tick']==tick,'noncontiguous original tick sequence')
        cmd = row['command']
        require(cmd is None if tick==0 else type(cmd) is list and len(cmd)==4 and
                all(type(v) is int for v in cmd) and cmd==commands[tick-1],
                f'original input/boundary mismatch at tick {tick}')
        state = row['state']
        require(type(state) is dict and set(state)=={'levelTime','rng','player','weapon','enemyBrains','projectiles','exitRequested'},'invalid original state schema')
        require(type(state['exitRequested']) is bool,'invalid original exit request')
        require(type(state['levelTime']) is int and 0<=state['levelTime']<2**32,'invalid level time')
        dc.integer_object(state['rng'],['play','misc'],'original RNG')
        require(all(0<=v<=255 for v in state['rng'].values()),'original RNG index out of range')
        player=state['player']
        require(type(player) is dict and set(player)==set(PLAYER_SCALARS)|{'ammo','pendingWeapon'},'invalid original player schema')
        dc.integer_object({k:player[k] for k in PLAYER_SCALARS},PLAYER_SCALARS,'original player')
        for key in PLAYER_SCALARS:
            value=player[key]
            require(0<=value<2**32 if key=='angle' else -2**31<=value<2**31,
                    f'original player {key} outside 32-bit range')
        require(type(player['ammo']) is list and len(player['ammo'])==4 and
                all(type(v) is int and -2**31<=v<2**31 for v in player['ammo']),'invalid original ammo array')
        require(player['pendingWeapon'] is None or type(player['pendingWeapon']) is int and
                0<=player['pendingWeapon']<9,'invalid original pending weapon')
        require(0<=player['readyWeapon']<9 and 0<=player['armorType']<=2,'invalid original weapon/armor type')
        dc.integer_object(state['weapon'],dc.WEAPON_FIELDS,'original weapon')
        require(all(-2**31<=v<2**31 for v in state['weapon'].values()),'weapon field outside 32-bit range')
        require(all(0<=state['weapon'][k]<SPEC['enemy_state_table']['count'] for k in ['state','flashState']),
                'invalid original psprite state')
        require(type(state['enemyBrains']) is dict,'invalid original enemy mapping')
        allowed={str(e['id']) for e in SPEC['enemy_profile']}
        dc.validate_projectiles(state['projectiles'])
        for shot in state['projectiles']:
            require(shot['source'] in {-1,0}|{int(i)+1 for i in allowed},'projectile source outside original enemy profile')
        require(set(state['enemyBrains'])<=allowed,'unknown original enemy identity')
        if tick==0: require(set(state['enemyBrains'])==allowed,'incomplete original enemy initialization')
        for brain in state['enemyBrains'].values():
            dc.integer_object(brain,dc.BRAIN_FIELDS,'original enemy brain')
            for key,value in brain.items():
                require(0<=value<2**32 if key=='angle' else -2**31<=value<2**31,'enemy field outside range')
            require(brain['target'] in {-1,0}|{int(i)+1 for i in allowed},'target outside original enemy profile')
            require(0<=brain['state']<SPEC['enemy_state_table']['count'] and 0<=brain['lastlook']<4,'invalid enemy state/look')
            require(brain['behaviorFlags'] & ~224 == 0,'invalid enemy behavior flags')
    return records


def read_records(path, commands):
    records = validate_records([json.loads(line) for line in Path(path).read_text().splitlines()], commands)
    require(all(r['state']['levelTime']==r['tick'] for r in records),'original level time mismatch')
    require(not any(r['state']['exitRequested'] for r in records[:-1]),'intermission beyond exit request unsupported')
    return records


def project(records, commands):
    result = []
    for row in records:
        dc.validate_state(row['state'])
        s = row['state']
        result.append({'tick':row['tick'],'command':row['command'],
                       'state':{'levelTime':s['levelTime'],'rng':s['rng'],
                                'player':{k:s['player'][k] for k in (*PLAYER_SCALARS,'ammo','pendingWeapon')},
                                'weapon':s['weapon'],'enemyBrains':s['enemyBrains'],'projectiles':s['projectiles'],
                                'exitRequested':s['exitRequested']}})
    return validate_records(result,commands)


def compare(original, candidate, commands, name):
    validate_records(original,commands); validate_records(candidate,commands)
    first = None; fields = {}
    for a,b in zip(original,candidate):
        diffs = [{'field':d['field'],'original':d['reference'],'candidate':d['lean']}
                 for d in dc.differences(a['state'],b['state'])]
        if diffs and first is None:
            first = {'tick':a['tick'],'phase':'initialization' if a['tick']==0 else 'after-tick',
                     'command':a['command'],'differences':diffs}
        for d in diffs: fields.setdefault(d['field'],{'tick':a['tick'],**d})
    return {'candidate':name,'status':'diverged' if first else 'match',
            'ticks_compared':len(commands),'initial_state_compared':True,
            'first_divergence':first,'first_by_field':fields}


def capture(binary, out, data):
    out = Path(out).resolve(); out.mkdir(parents=True,exist_ok=True)
    commands = dc.decode_demo(data)
    for name in ['original.jsonl','binding.json','capture.json']:
        (out/name).unlink(missing_ok=True)
    # A dedicated mount prevents DOS from seeing other project or home files.
    mount = out/'dos'; mount.mkdir(exist_ok=True)
    require(not any(c in str(mount) for c in ['"','\r','\n']),'unsupported quote/newline in DOS mount path')
    exe = original_image()
    wad = (ROOT/'artifacts/doom-shareware-1.9/doom1.wad').read_bytes()
    require(sha(wad)==SHAREWARE['wad_sha256'],'shareware WAD hash mismatch')
    (mount/'DOOM.EXE').write_bytes(exe); (mount/'DOOM1.WAD').write_bytes(wad)
    (mount/'INPUT.LMP').write_bytes(data)
    (mount/'DEFAULT.CFG').write_text('snd_musicdevice 0\nsnd_sfxdevice 0\n')
    config = f'''[sdl]
fullscreen=false
output=surface
autolock=false
waitonerror=false
[dosbox]
machine=svga_s3
memsize=32
[cpu]
core=normal
cputype=486
cycles=fixed 30000
[mixer]
nosound=true
[midi]
mididevice=none
[sblaster]
sbtype=none
[gus]
gus=false
[autoexec]
mount c "{mount}"
c:
doom.exe -timedemo input -nodraw -nosound -config default.cfg
exit
'''
    (out/'dosbox.conf').write_text(config)
    env = {**os.environ,'SDL_VIDEODRIVER':'dummy','SDL_AUDIODRIVER':'dummy',
           'LEANDOOM_DOS_TRACE':str(out/'original.jsonl'),
           'LEANDOOM_DOS_TICS':str(len(commands)), 'LEANDOOM_DOS_BINDING':str(out/'binding.json')}
    with (out/'emulator.log').open('w') as log:
        subprocess.run([str(binary),'-conf',str(out/'dosbox.conf'),'-noconsole','-fastlaunch'],
                       cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120)
    require((mount/'DOOM.EXE').read_bytes()==exe,'guest executable changed during run')
    require((mount/'DOOM1.WAD').read_bytes()==wad and (mount/'INPUT.LMP').read_bytes()==data,
            'guest inputs changed during run')
    records = read_records(out/'original.jsonl',commands)
    binding = json.loads((out/'binding.json').read_text())
    require(binding.get('paging') is False,'unsupported paged memory binding')
    require(all(type(binding.get(k)) is int and 0<=binding[k]<32*1024*1024
                for k in ['code_linear','data_linear','ds_base']),'invalid runtime address binding')
    evidence = {'exe_sha256':sha(exe),'wad_sha256':sha(wad),'demo_sha256':sha(data),
                'config_sha256':sha(config.encode()),'binding':binding,
                'emulator_executable_sha256':sha(Path(binary).read_bytes()),
                'trace_sha256':sha((out/'original.jsonl').read_bytes())}
    (out/'capture.json').write_text(json.dumps(evidence,indent=2)+'\n')
    return records,evidence


def run(args):
    out = Path(args.out).resolve(); out.mkdir(parents=True,exist_ok=True)
    for name in ['report.json','provenance.json']: (out/name).unlink(missing_ok=True)
    original_image()  # Reject missing/wrong assets before an expensive build.
    binary,identity = build_emulator(args.fetch,args.rebuild)
    dc.run(argparse.Namespace(out=str(out/'diagnostic'),demo=args.demo,scenario=args.scenario,
                              ticks=args.ticks,fetch=args.fetch))
    data = (out/'diagnostic/input.lmp').read_bytes(); commands = dc.decode_demo(data)
    original,evidence = capture(binary,out,data)
    results = {}
    for name,filename in [('chocolate','reference.jsonl'),('lean','lean.jsonl')]:
        candidate = project(dc.read_records(out/'diagnostic'/filename),commands)
        results[name] = compare(original,candidate,commands,name)
    provenance = {'schema':SPEC['schema'],'emulator_build':identity,'original':evidence,
                  'diagnostic':json.loads((out/'diagnostic/provenance.json').read_text())}
    (out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    report = {'schema':SPEC['schema'],'oracle':'Unmodified DOOM shareware 1.9 EXE running in instrumented DOSBox-X',
              'profile':dc.SPEC['profile'],'boundary':dc.SPEC['boundary'],
              'coverage':SPEC['compared'],'excluded':SPEC['excluded'],
              'provenance_verified':True,'comparisons':results,
              'status':'match' if all(r['status']=='match' for r in results.values()) else 'diverged'}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--demo'); parser.add_argument('--scenario',choices=dc.SCENARIOS,default='movement')
    parser.add_argument('--ticks',type=int,default=200); parser.add_argument('--fetch',action='store_true')
    parser.add_argument('--rebuild',action='store_true',help='discard the emulator build cache')
    parser.add_argument('--out',default=str(ROOT/'artifacts/original-comparison'))
    args = parser.parse_args(); report = run(args)
    for name,r in report['comparisons'].items():
        print(f"Original vs {name}: {r['status']} (initialization + {r['ticks_compared']} tics; declared fields only)")
        if r['first_divergence']:
            d = r['first_divergence']; print(f"  First difference at tick {d['tick']}: {d['differences']}")
    print(f"Report: {Path(args.out).resolve()/'report.json'}")
    return 1 if report['status']=='diverged' else 0


if __name__=='__main__':
    try: sys.exit(main())
    except (ValueError, OSError, subprocess.SubprocessError, tarfile.TarError, struct.error) as error:
        print(f'original comparison error: {error}',file=sys.stderr); sys.exit(2)

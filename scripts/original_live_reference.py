"""Pinned DOSBox-X builder for the original DOOM live observer."""
import json
from pathlib import Path
import shutil
import struct
import subprocess
import tarfile

import original_demo_compare as oc
ROOT=oc.ROOT
SPEC=json.loads((ROOT/'tests/reference/original-live.json').read_text())


def verify_profile():
    image=oc.original_image()
    code,*_=oc.mul.inspect_image(image,oc.PROFILE)
    for name,item in SPEC['evidence'].items():
        p=int(item['offset'],16);raw=bytes.fromhex(item['hex'])
        oc.require(code[p:p+len(raw)]==raw,f'original live instruction evidence mismatch: {name}')
    relocations=oc.fixups(image,range((len(code)+4095)//4096))
    for operand,target in SPEC['data_operands'].items():
        p,t=int(operand,16),int(target,16)
        oc.require(struct.unpack_from('<I',code,p)[0]==t and (p,3,t) in relocations,
                   f'original live data relocation mismatch: {operand}')
    return image


def declarations():
    spec=oc.SPEC
    text='static const int ld_enemy_ids[] = {'+','.join(str(e['id']) for e in spec['enemy_profile'])+'};\n'
    text+='static const int ld_enemy_spawns[][5] = {'+','.join('{'+','.join(map(str,e['spawn']))+'}' for e in spec['enemy_profile'])+'};\n'
    text+='static const unsigned ld_enemy_types[] = {'+','.join(str(e['type']) for e in spec['enemy_profile'])+'};\n'
    for group in ['enemy','player','psprite','projectile']:
        prefix='ld_' if group=='enemy' else f'ld_{group}_'
        text+=''.join(f'static const unsigned {prefix}{k}={v};\n' for k,v in spec[group+'_offsets'].items())
    text+=''.join(f'static const unsigned ld_{k}={v};\n' for k,v in spec['player_layout'].items())
    text+=''.join(f'static const unsigned ld_shot_{k}={v};\n' for k,v in spec['projectile_layout'].items())
    return text


def build_reference(fetch=False):
    verify_profile()
    archive=ROOT/'artifacts/reference/dosbox-x-e013b8bf.tar.gz'
    if not archive.exists():oc.build_emulator(fetch=fetch)
    oc.require(oc.sha(archive.read_bytes())==oc.SPEC['emulator']['archive_sha256'],'DOSBox source hash mismatch')
    work=ROOT/'artifacts/original-live-reference';work.mkdir(parents=True,exist_ok=True)
    source=work/f'dosbox-x-{oc.SPEC["emulator"]["commit"]}'
    binary=source/'src/dosbox-x'
    observer=(ROOT/'tests/reference/dosbox_tick_trace.h').read_text()
    adapter=(ROOT/'tests/reference/dosbox_live_frame.h').read_text()
    identity={'emulator':oc.SPEC['emulator'],'builder':oc.sha(Path(__file__).read_bytes()),
              'original_helper':oc.sha(Path(oc.__file__).read_bytes()),
              'observer':oc.sha(observer.encode()),'adapter':oc.sha(adapter.encode()),
              'profile':oc.sha(json.dumps([oc.SPEC,SPEC],sort_keys=True).encode()),'configure':oc.CONFIGURE}
    stamp=work/'build.json'
    if stamp.exists() and binary.exists():
        saved=json.loads(stamp.read_text())
        if saved.get('inputs')==identity and saved.get('executable_sha256')==oc.sha(binary.read_bytes()):return binary,saved
    stamp.unlink(missing_ok=True)
    if source.exists():shutil.rmtree(source)
    with tarfile.open(archive) as tar:tar.extractall(work,filter='data')
    # Keep the established offline observer byte-for-byte in the repository.
    # The live variant retains its trace but doesn't exit before rendering.
    observer=observer.replace('/* ENEMY_PROFILE */',declarations())
    observer=oc.dc.replace_once(observer,'std::fopen(output,"w")','std::fopen(output,"w+")')
    observer=oc.dc.replace_once(observer,'(rd(data+0x2b2f8)!=0 || tick!=limit)','rd(data+0x2b2f8)!=0')
    observer=oc.dc.replace_once(observer,'if(tick==limit) { if(std::fclose(trace)) fail("trace close failed"); std::exit(0); }','LDLiveState(trace,tick);')
    core=source/'src/cpu/core_normal.cpp'
    text=oc.dc.replace_once(core.read_text(),'Bits CPU_Core_Normal_Run(void) {',
         '#include "dosbox_live_frame.h"\n#include "dosbox_tick_trace.h"\n\nBits CPU_Core_Normal_Run(void) {')
    oc.require('\t\tLOADIP;' in text,'normal core boundary missing')
    text=text.replace('\t\tLOADIP;','\t\tLOADIP;\n        LDLiveObserve(core.cseip);\n        LeanDoomObserve(core.cseip);',1)
    core.write_text(text)
    (core.parent/'dosbox_tick_trace.h').write_text(observer)
    (core.parent/'dosbox_live_frame.h').write_text(adapter)
    with (work/'build.log').open('w') as log:
        for command in [['./autogen.sh'],['./configure',*oc.CONFIGURE],['make','-j4']]:
            subprocess.run(command,cwd=source,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
    saved={'inputs':identity,'executable_sha256':oc.sha(binary.read_bytes())}
    stamp.write_text(json.dumps(saved,indent=2)+'\n')
    return binary,saved


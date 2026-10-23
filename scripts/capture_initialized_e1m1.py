#!/usr/bin/env python3
"""Opt-in pinned pre-first-P_Ticker RAM capture; preserves old observer/builds."""
import json
import os
from pathlib import Path
import subprocess
import tarfile
import sys
sys.setrecursionlimit(10000)
import original_demo_compare as oc
import original_live_reference as live

ROOT = oc.ROOT
OUT = ROOT/'artifacts/initialized-e1m1'

def build():
    oc.original_image()
    archive = ROOT/'artifacts/reference/dosbox-x-e013b8bf.tar.gz'
    oc.require(oc.sha(archive.read_bytes()) == oc.SPEC['emulator']['archive_sha256'], 'source pin')
    hook = ROOT/'tests/reference/dosbox_initialized_snapshot.h'
    observer = ROOT/'tests/reference/dosbox_tick_trace.h'
    identity = {str(p.relative_to(ROOT)): oc.sha(p.read_bytes()) for p in
                [Path(__file__), hook, observer, Path(oc.__file__), Path(live.__file__),
                 ROOT/'tests/reference/original-tick.json']}
    identity['archive'] = oc.sha(archive.read_bytes())
    identity['configure'] = oc.CONFIGURE
    work = OUT/'emulator'; work.mkdir(parents=True, exist_ok=True)
    stamp = work/'build.json'
    source = work/f"dosbox-x-{oc.SPEC['emulator']['commit']}"
    binary = source/'src/dosbox-x'
    if stamp.exists() and binary.exists():
        saved = json.loads(stamp.read_text())
        if saved['inputs'] == identity and saved['binary'] == oc.sha(binary.read_bytes()):
            return binary, saved
    if not source.exists():
        with tarfile.open(archive) as tar:
            tar.extractall(work, filter='data')
    core = source/'src/cpu/core_normal.cpp'
    # Always generate the changed translation unit from the pinned archive.
    with tarfile.open(archive) as tar:
        original = tar.extractfile(f'{source.name}/src/cpu/core_normal.cpp').read().decode()
    original = oc.dc.replace_once(original, 'Bits CPU_Core_Normal_Run(void) {',
        '#include "dosbox_initialized_snapshot.h"\n#include "dosbox_tick_trace.h"\n\nBits CPU_Core_Normal_Run(void) {')
    oc.require('\t\tLOADIP;' in original, 'normal core boundary missing')
    original = original.replace('\t\tLOADIP;', '\t\tLOADIP;\n        LeanDoomObserve(core.cseip);', 1)
    core.write_text(original)
    text = observer.read_text().replace('/* ENEMY_PROFILE */', live.declarations())
    text = oc.dc.replace_once(text, '    std::fprintf(trace,"{\\\"tick\\\":%u,\\\"command\\\":",tick);',
        '    LDInitialSnapshot(code,data,dsbase,tick);\n    std::fprintf(trace,"{\\\"tick\\\":%u,\\\"command\\\":",tick);')
    (core.parent/'dosbox_tick_trace.h').write_text(text)
    (core.parent/hook.name).write_bytes(hook.read_bytes())
    with (work/'build.log').open('w') as log:
        commands = [['make','-j4']] if (source/'Makefile').exists() else [
            ['./autogen.sh'], ['./configure', *oc.CONFIGURE], ['make','-j4']]
        for command in commands:
            subprocess.run(command,cwd=source,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=500)
    saved = {'inputs':identity, 'binary':oc.sha(binary.read_bytes()),
             'generated_core':oc.sha(core.read_bytes()), 'generated_observer':oc.sha(text.encode()),
             'trust':'local source/build/hash bookkeeping, not reproducible-build attestation'}
    stamp.write_text(json.dumps(saved,indent=2)+'\n')
    return binary,saved

def main():
    binary, build_info = build()
    out = OUT/'capture'; out.mkdir(parents=True,exist_ok=True)
    os.environ['LEANDOOM_INITIAL_DIR'] = str(out.resolve())
    commands = [[0,0,0,0]]
    records, evidence = oc.capture(binary,out,oc.dc.encode_demo(commands))
    meta = json.loads((out/'initial.json').read_text())
    oc.require(meta['leveltime']==0 and meta['pc']==0x2081a, 'initial boundary')
    evidence.update({'boundary':'first pre-P_Ticker CALL at code+0x2081a; leveltime=0; before gameplay and any opening wipe',
        'commands':commands,'presentation':'-timedemo -nodraw -nosound; no claim about a presented frame',
        'raw_ram_sha256':oc.sha((out/'ram.bin').read_bytes()),
        'raw_vram_sha256':oc.sha((out/'vram.bin').read_bytes()),
        'metadata_sha256':oc.sha((out/'initial.json').read_bytes()),'build':build_info,
        'omitted':'device control registers, scheduler and emulator internals; not a restartable save-state'})
    (out/'provenance.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps({'capture':'actual pinned DOS','boundary':meta,'rng':records[0]['state']['rng']}))

if __name__ == '__main__':
    main()

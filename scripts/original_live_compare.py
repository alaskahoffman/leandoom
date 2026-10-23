#!/usr/bin/env python3
"""Live DOS shareware 1.9 versus Lean; original executable, emulator input adapter."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

import live_compare as live
import original_demo_compare as oc
from original_live_reference import SPEC, verify_profile, build_reference

ROOT=oc.ROOT


class ProjectedReader:
    def __init__(self,fd):self.reader=live.PacketReader(fd)
    def packet(self):
        record,frame=self.reader.packet(timeout=60)
        s=record['state'];oc.dc.validate_state(s)
        state={'levelTime':s['levelTime'],'rng':s['rng'],
               'player':{k:s['player'][k] for k in (*oc.PLAYER_SCALARS,'ammo','pendingWeapon')},
               'weapon':s['weapon'],'enemyBrains':s['enemyBrains'],'projectiles':s['projectiles'],
               'exitRequested':s['exitRequested']}
        return {**record,'state':state},frame


class Session(live.Session):
    reference_label='DOS Doom 1.9'
    reference_note='Original shareware executable · raw VGA frame / pre-DAC palette · selected DOS gameplay fields · silent · E1M1 only'
    def reset(self):
        self.close();self.generation+=1
        self.directory=self.out/f'run-{time.time_ns()}';self.directory.mkdir(parents=True)
        self.commands=[];self.held=0;self.first_difference=None;self.last=None;self.ended=False;self.failed=False
        mount=self.directory/'dos';mount.mkdir()
        oc.require(not any(c in str(mount) for c in ['"','\r','\n']),'invalid mount path')
        image=verify_profile();wad=self.wad.read_bytes()
        oc.require(oc.sha(wad)==oc.SHAREWARE['wad_sha256'],'DOS live profile requires pinned shareware WAD')
        (mount/'DOOM.EXE').write_bytes(image);(mount/'DOOM1.WAD').write_bytes(wad)
        (mount/'INPUT.LMP').write_bytes(oc.dc.HEADER+b'\0'*40000+b'\x80')
        (mount/'DEFAULT.CFG').write_text('screenblocks 10\ndetaillevel 0\nusegamma 0\nshow_messages 1\nsnd_musicdevice 0\nsnd_sfxdevice 0\n')
        config=f'''[sdl]
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
cycles=max
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
doom.exe -timedemo input -nosound -config default.cfg
exit
'''
        (self.directory/'dosbox.conf').write_text(config)
        self.command_file=(self.directory/'commands.txt').open('w');self.files.append(self.command_file)
        ref_log=(self.directory/'reference.log').open('wb');lean_log=(self.directory/'lean.log').open('wb');self.files += [ref_log,lean_log]
        read_fd,write_fd=os.pipe();self.reply=read_fd
        env={**os.environ,'SDL_VIDEODRIVER':'dummy','SDL_AUDIODRIVER':'dummy',
             'LEANDOOM_REPLY_FD':str(write_fd),'LEANDOOM_DOS_TRACE':str(self.directory/'original.jsonl'),
             'LEANDOOM_DOS_BINDING':str(self.directory/'binding.json'),'LEANDOOM_DOS_TICS':'10000'}
        try:
            ref=subprocess.Popen([str(self.binary),'-conf',str(self.directory/'dosbox.conf'),'-noconsole','-fastlaunch'],
                 cwd=self.directory,env=env,stdin=subprocess.PIPE,stdout=ref_log,stderr=ref_log,pass_fds=(write_fd,))
            self.processes.append(ref)
        finally:os.close(write_fd)
        lean=subprocess.Popen([str(ROOT/'.lake/build/bin/live-render-probe'),str(self.wad),'--dos-presentation'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=lean_log)
        self.processes.append(lean)
        self.readers=[live.PacketReader(read_fd),ProjectedReader(lean.stdout.fileno())]
        self.provenance={'oracle':'Original DOS DOOM shareware 1.9 executable in DOSBox-X; live demo-input adapter',
             'doom_executable_sha256':oc.sha(image),'emulator_build':self.build_key,
             'lean_executable_sha256':oc.sha((ROOT/'.lake/build/bin/live-render-probe').read_bytes()),
             'wad_sha256':oc.sha(wad),'config_sha256':oc.sha(config.encode()),
             'presentation':'Original Mode X back page after D_Display drawing, before flip/wipe; raw palette before DAC quantization; one render per tic; silent',
             'state_schema':oc.SPEC['schema'],'input_capacity':10000,
             'lean_guest_memory':{'profile':'dos-shareware-e1m1-silent-v1',
                 'zone_base':'0x28e024','zone_bytes':8388608,'lump_cells':'0xa8f024',
                 'ordering':'Generated independently by Lean startup, gameplay and rendering',
                 'unknown_payload_reads':'Error; no pixel fallback'}}
        (self.directory/'provenance.json').write_text(json.dumps(self.provenance,indent=2))
    def step(self,cmd):
        oc.require(len(self.commands)<10000,'DOS demo buffer exhausted; restart comparison.')
        oc.require(len(cmd)==4 and type(cmd[3]) is int and 0<=cmd[3]<128,'DOS live profile excludes special pause/save commands')
        return super().step(cmd)
    def save(self):
        mount=self.directory/'dos'
        oc.require(oc.sha((mount/'DOOM.EXE').read_bytes())==self.provenance['doom_executable_sha256'],
                   'DOS executable changed during capture')
        oc.require(oc.sha((mount/'DOOM1.WAD').read_bytes())==self.provenance['wad_sha256'],
                   'DOS WAD changed during capture')
        oc.require((mount/'INPUT.LMP').read_bytes()==oc.dc.HEADER+b'\0'*40000+b'\x80',
                   'DOS on-disk input buffer changed during capture')
        folder=Path(super().save())
        for name in ['binding.json','original.jsonl']:
            (folder/name).write_bytes((self.directory/name).read_bytes())
        return str(folder)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--port',type=int,default=0)
    p.add_argument('--out',type=Path,default=ROOT/'artifacts/dos-live-compare')
    p.add_argument('--replay',type=Path)
    p.add_argument('--check',action='store_true')
    p.add_argument('--fetch',action='store_true')
    args=p.parse_args()
    oc.require(not args.check or args.replay is not None,'--check requires --replay')
    print('Building original DOS live comparison…',flush=True)
    subprocess.run([str(ROOT/'scripts/lake'),'build','live-render-probe'],cwd=ROOT,check=True)
    binary,key=build_reference(args.fetch)
    session=Session(ROOT/'artifacts/doom-shareware-1.9/doom1.wad',binary,key,args.out)
    try:
        if args.replay:
            for line in args.replay.read_text().splitlines():
                if line.strip():session.step([int(n) for n in line.split()])
            print('Replay capture: '+session.save(),flush=True)
        if args.check:return
        httpd=live.server(session,args.port)
        print(f'LIVE_COMPARISON_URL=http://127.0.0.1:{httpd.server_port}/',flush=True)
        try:httpd.serve_forever()
        finally:httpd.server_close()
    finally:session.close()

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Local, tic-locked E1M1 pixel comparison. No changes to the offline oracle."""
import argparse
import html
import http.server
import json
import os
from pathlib import Path
import secrets
import select
import shutil
import struct
import subprocess
import tarfile
import threading
import time

import demo_compare as dc
import render_compare as rc

ROOT=dc.ROOT
FRAME_SIZE=320*200*3


def build_reference(fetch=False):
    archive=ROOT/'artifacts/reference/chocolate-doom-3.1.1-full.tar.gz'
    if not archive.exists():
        dc.require(fetch,'Pinned reference archive missing; use --fetch once.')
        # The existing builder owns download/hash verification.
        dc.build_reference(fetch=True)
    dc.require(dc.sha(archive.read_bytes())==dc.SPEC['archive_sha256'],'reference archive hash mismatch')
    work=ROOT/'artifacts/live-render-reference';work.mkdir(parents=True,exist_ok=True)
    source=work/f'chocolate-doom-{dc.SPEC["commit"]}'
    observer=(ROOT/'tests/reference/tick_trace.inc').read_text()
    adapter=(ROOT/'tests/reference/live_frame.inc').read_text()
    key=dc.sha((Path(__file__).read_text()+observer+adapter+dc.SPEC['archive_sha256']).encode())
    stamp=work/'build-key';binary=work/'build/src/chocolate-doom'
    if binary.exists() and stamp.exists() and stamp.read_text()==key:return binary,key
    if source.exists():shutil.rmtree(source)
    with tarfile.open(archive) as tar:tar.extractall(work,filter='data')
    for name,digest in json.loads((ROOT/'tests/reference/manifest.json').read_text())['files'].items():
        dc.require(dc.sha((source/name).read_bytes())==digest,f'reference file hash mismatch: {name}')
    # Reuse the declared-state observer. Its original offline file is untouched.
    observer=observer[:observer.index('static void LTraceBefore(void)')]+r'''
static void LTraceBefore(void)
{
    if(ltrace_file) return;
    const char *fd=getenv("LEANDOOM_REPLY_FD");
    if(!fd) I_Error("live comparison: missing reply descriptor");
    ltrace_file=fdopen(atoi(fd),"wb");
    if(!ltrace_file) I_Error("live comparison: cannot open reply");
}
static void LTraceAfter(void)
{
    ++ltrace_tick;
    LTraceWrite(0);
    LLiveFrame(ltrace_file);
}
'''
    doom=source/'src/doom';(doom/'tick_trace.inc').write_text(adapter+'\n'+observer)
    p=doom/'g_game.c';s=p.read_text()
    s=dc.replace_once(s,'void G_Ticker (void)','#include "tick_trace.inc"\n\nvoid G_Ticker (void)')
    s=dc.replace_once(s,'\tP_Ticker ();','\tLTraceBefore();\n\tP_Ticker ();')
    s=dc.replace_once(s,'\tHU_Ticker ();','\tHU_Ticker ();\n\tLTraceAfter();')
    # Override only the demo input boundary, before upstream command processing.
    s=dc.replace_once(s,'void G_ReadDemoTiccmd (ticcmd_t* cmd) \n{ ',
                      'void G_ReadDemoTiccmd (ticcmd_t* cmd) \n{ LLiveCommand(cmd); return; ')
    p.write_text(s)
    p=doom/'p_setup.c';p.write_text('extern int LTraceMapIndex;\n'+dc.replace_once(p.read_text(),'\tP_SpawnMapThing(&spawnthing);','\tLTraceMapIndex=i;\n\tP_SpawnMapThing(&spawnthing);\n\tLTraceMapIndex=-1;'))
    p=doom/'p_mobj.c';s=p.read_text()
    s=dc.replace_once(s,'    P_AddThinker (&mobj->thinker);','    P_AddThinker (&mobj->thinker);\n    LTraceSpawn(mobj);')
    s=dc.replace_once(s,'void P_RemoveMobj (mobj_t* mobj)\n{','void P_RemoveMobj (mobj_t* mobj)\n{\n    LTraceRemove(mobj);')
    s=dc.replace_once(s,'#include "p_local.h"','#include "p_local.h"\nvoid LTraceSpawn(mobj_t *mo);\nvoid LTraceRemove(mobj_t *mo);');p.write_text(s)
    p=source/'src/i_video.c';p.write_text(dc.replace_once(p.read_text(),'void I_SetPalette (byte *doompalette)\n{','unsigned char LRenderPalette[768];\nvoid I_SetPalette (byte *doompalette)\n{\n    memcpy(LRenderPalette,doompalette,768);'))
    with (work/'build.log').open('w') as log:
        subprocess.run(['cmake','-S',str(source),'-B',str(work/'build'),'-DENABLE_SDL2_MIXER=OFF','-DENABLE_SDL2_NET=OFF','-DCMAKE_BUILD_TYPE=Release','-DCMAKE_C_FLAGS=-fwrapv','-DCMAKE_POLICY_VERSION_MINIMUM=3.5'],stdout=log,stderr=log,check=True)
        subprocess.run(['cmake','--build',str(work/'build'),'--target','chocolate-doom','-j','4'],stdout=log,stderr=log,check=True)
    stamp.write_text(key)
    return binary,key


class PacketReader:
    """Bounded reads prevent a failed worker from hanging the browser forever."""
    def __init__(self,fd):self.fd=fd;self.buffer=bytearray()
    def packet(self,timeout=15):
        deadline=time.monotonic()+timeout
        def fill():
            left=deadline-time.monotonic()
            if left<=0 or not select.select([self.fd],[],[],left)[0]:raise TimeoutError('engine response timed out')
            data=os.read(self.fd,262144)
            if not data:raise RuntimeError('engine stopped; inspect session logs')
            self.buffer.extend(data)
        while b'\n' not in self.buffer:
            if len(self.buffer)>2_000_000:raise ValueError('oversize engine record')
            fill()
        end=self.buffer.index(10)
        record=json.loads(self.buffer[:end]);del self.buffer[:end+1]
        while len(self.buffer)<FRAME_SIZE:fill()
        frame=bytes(self.buffer[:FRAME_SIZE]);del self.buffer[:FRAME_SIZE]
        return record,frame


class Session:
    def __init__(self,wad,binary,build_key,out):
        self.wad=Path(wad).resolve();self.binary=binary;self.build_key=build_key;self.out=Path(out).resolve()
        self.processes=[];self.files=[];self.reply=None;self.generation=0
        self.lock=threading.Lock();self.reset()
    def close(self):
        for p in self.processes:
            if p.stdin:p.stdin.close()
            if p.poll() is None:
                p.terminate()
                try:p.wait(timeout=2)
                except subprocess.TimeoutExpired:p.kill();p.wait()
            if p.stdout:p.stdout.close()
        self.processes=[]
        if self.reply is not None:os.close(self.reply);self.reply=None
        for f in self.files:f.close()
        self.files=[]
    def reset(self):
        self.close();self.generation+=1
        self.directory=self.out/f'run-{time.time_ns()}';self.directory.mkdir(parents=True)
        self.commands=[];self.held=0;self.first_difference=None;self.last=None;self.ended=False;self.failed=False
        (self.directory/'input.lmp').write_bytes(dc.HEADER+b'\x80')
        (self.directory/'default.cfg').write_text('screenblocks 10\ndetaillevel 0\nusegamma 0\nshow_messages 1\n')
        (self.directory/'chocolate.cfg').write_text('')
        self.command_file=(self.directory/'commands.txt').open('w');self.files.append(self.command_file)
        ref_log=(self.directory/'reference.log').open('wb');lean_log=(self.directory/'lean.log').open('wb');self.files += [ref_log,lean_log]
        read_fd,write_fd=os.pipe();self.reply=read_fd
        env={**os.environ,'SDL_VIDEODRIVER':'dummy','SDL_AUDIODRIVER':'dummy','LEANDOOM_TRACE':'live','LEANDOOM_REPLY_FD':str(write_fd)}
        try:
            ref=subprocess.Popen([str(self.binary),'-iwad',str(self.wad),'-timedemo',str(self.directory/'input.lmp'),'-gameversion','1.9','-nodraw','-nosound','-nojoy','-nomouse','-config',str(self.directory/'default.cfg'),'-extraconfig',str(self.directory/'chocolate.cfg')],cwd=self.directory,env=env,stdin=subprocess.PIPE,stdout=ref_log,stderr=ref_log,pass_fds=(write_fd,))
            self.processes.append(ref)
        finally:os.close(write_fd)
        lean=subprocess.Popen([str(ROOT/'.lake/build/bin/live-render-probe'),str(self.wad)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=lean_log)
        self.processes.append(lean)
        self.readers=[PacketReader(read_fd),PacketReader(lean.stdout.fileno())]
        self.provenance={'oracle':'Pinned Chocolate DOOM, live command adapter; not DOS','commit':dc.SPEC['commit'],'archive_sha256':dc.SPEC['archive_sha256'],'adapter_build_key':self.build_key,'reference_executable_sha256':dc.sha(self.binary.read_bytes()),'lean_executable_sha256':dc.sha((ROOT/'.lake/build/bin/live-render-probe').read_bytes()),'wad_sha256':dc.sha(self.wad.read_bytes()),'presentation':'one render per input tic; 320x200; screenblocks 10; raw palette; retained fuzz phase; normal incremental Chocolate HUD; silent'}
        (self.directory/'provenance.json').write_text(json.dumps(self.provenance,indent=2))
    def command(self,keys):
        # G_BuildTiccmd keyboard subset, then vanilla short-tic demo quantization.
        down=lambda bit:bool(keys&bit)
        self.held=self.held+1 if down(32) or down(64) else 0
        turn=320 if self.held<6 else (1280 if down(512) else 640)
        f=(int(down(2))-int(down(4)))*(50 if down(512) else 25)
        s=(int(down(16))-int(down(8)))*(40 if down(512) else 24)
        a=((int(down(32))-int(down(64)))*turn+128)//256*256
        b=int(down(8192))+2*int(down(4096))
        for bit,weapon in [(16384,0),(32768,1),(65536,2)]:
            if down(bit):b|=4+(weapon<<3);break
        return [f,s,a,b]
    def step(self,cmd):
        if self.failed:raise ValueError('Worker failed; restart the comparison.')
        if self.ended:raise ValueError('E1M1 exit reached; restart the comparison.')
        dc.require(len(cmd)==4 and all(type(n) is int for n in cmd),'invalid ticcmd')
        f,s,a,b=cmd
        dc.require(-127<=f<=127 and -128<=s<=127 and -32768<=a<=32512 and a%256==0 and 0<=b<=255,'invalid ticcmd range')
        line=' '.join(map(str,cmd))+'\n'
        try:
            for p in self.processes:p.stdin.write(line.encode());p.stdin.flush()
            results=[r.packet() for r in self.readers]
            tick=len(self.commands)+1
            for record,_ in results:
                dc.require(record['tick']==tick and record['command']==cmd,'engine tick/command desynchronization')
            self.commands.append(cmd);self.command_file.write(line);self.command_file.flush()
            ref,lean=results[0][0],results[1][0]
            different=next(iter(dc.differences(ref['state'],lean['state'])),None)
            if different is not None and self.first_difference is None:self.first_difference={'tick':tick,'difference':different}
            self.ended=bool(ref['state']['exitRequested'] or lean['state']['exitRequested'])
            meta={'tick':tick,'generation':self.generation,'gameplayMatch':different is None,'firstStateDifference':self.first_difference,'exitReached':self.ended}
            self.last=(meta,results)
            return meta,results[0][1],results[1][1]
        except Exception:
            self.failed=True
            raise
    def save(self):
        dc.require(self.last is not None,'Play at least one tic before saving.')
        meta,results=self.last;folder=self.directory/f'capture-{meta["tick"]}'
        folder.mkdir(exist_ok=True)
        (folder/'commands.txt').write_text(''.join(' '.join(map(str,c))+'\n' for c in self.commands))
        (folder/'input.lmp').write_bytes(dc.HEADER+b''.join(struct.pack('<bbBB',c[0],c[1],(c[2]>>8)&255,c[3]) for c in self.commands)+b'\x80')
        for name,(record,frame) in zip(['reference','lean'],results):
            (folder/f'{name}.json').write_text(json.dumps(record,indent=2))
            (folder/f'{name}.ppm').write_bytes(b'P6\n320 200\n255\n'+frame)
            (folder/f'{name}.png').write_bytes(rc.png(frame))
        ref,lean=results[0][1],results[1][1]
        diff=rc.diff_ppm(ref,lean);(folder/'difference.ppm').write_bytes(diff);(folder/'difference.png').write_bytes(rc.png(diff.split(b'\n',3)[3]))
        report={**self.provenance,**meta,**rc.compare_pixels(ref,lean),'commands_sha256':dc.sha((folder/'commands.txt').read_bytes())}
        (folder/'report.json').write_text(json.dumps(report,indent=2))
        return str(folder)


def server(session,port=0):
    token=secrets.token_urlsafe(24)
    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self,*args):pass
        def send(self,status,data,kind='application/json'):
            self.send_response(status);self.send_header('Content-Type',kind)
            self.send_header('Content-Length',str(len(data)));self.send_header('Cache-Control','no-store')
            self.send_header('X-Content-Type-Options','nosniff');self.end_headers();self.wfile.write(data)
        def do_GET(self):
            if self.headers.get('Host')!=f'127.0.0.1:{self.server.server_port}':self.send(403,b'{}');return
            if self.path!='/':self.send(404,b'{}');return
            page=(ROOT/'web/live-compare/index.html').read_text().replace('__TOKEN__',token)
            page=page.replace('Chocolate',html.escape(getattr(session,'reference_label','Chocolate')))
            page=page.replace('<p class="muted" id="reference-note"></p>','<p class="muted" id="reference-note">'+html.escape(getattr(session,'reference_note',''))+'</p>')
            self.send(200,page.encode(),'text/html; charset=utf-8')
        def do_POST(self):
            # Loopback binding plus a per-server capability blocks cross-site control.
            if self.headers.get('Host')!=f'127.0.0.1:{self.server.server_port}' or self.headers.get('X-Compare-Token')!=token:self.send(403,b'{"error":"Forbidden"}');return
            try:
                size=int(self.headers.get('Content-Length','0'))
                dc.require(0<size<=4096,'invalid request size')
                body=json.loads(self.rfile.read(size))
                with session.lock:
                    if self.path=='/reset':
                        session.reset();answer={'tick':0,'generation':session.generation}
                    elif self.path=='/step':
                        dc.require(body.get('generation')==session.generation and body.get('tick')==len(session.commands),'Stale window: restart or reload this comparison.')
                        keys=body.get('keys',0);dc.require(type(keys) is int and 0<=keys<131072,'invalid controls')
                        meta,ref,lean=session.step(session.command(keys))
                        header=json.dumps(meta,separators=(',',':')).encode()
                        self.send(200,struct.pack('<I',len(header))+header+ref+lean,'application/octet-stream');return
                    elif self.path=='/save':answer={'path':session.save()}
                    elif self.path=='/frame':
                        dc.require(session.last is not None,'No frame yet.')
                        meta,results=session.last
                        header=json.dumps(meta,separators=(',',':')).encode()
                        self.send(200,struct.pack('<I',len(header))+header+results[0][1]+results[1][1],'application/octet-stream');return
                    elif self.path=='/status':answer={'tick':len(session.commands),'generation':session.generation}
                    else:self.send(404,b'{}');return
                self.send(200,json.dumps(answer).encode())
            except Exception as error:self.send(400,json.dumps({'error':str(error)}).encode())
    return http.server.ThreadingHTTPServer(('127.0.0.1',port),Handler)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wad',type=Path,default=ROOT/'artifacts/doom-shareware-1.9/doom1.wad')
    parser.add_argument('--port',type=int,default=0)
    parser.add_argument('--out',type=Path,default=ROOT/'artifacts/live-compare')
    parser.add_argument('--fetch',action='store_true')
    parser.add_argument('--reference',choices=['chocolate','dos'],default='chocolate',
                        help='Original DOS executable or native Chocolate reference')
    parser.add_argument('--replay',type=Path,help='Replay a saved commands.txt before opening the paused view')
    parser.add_argument('--check',action='store_true',help='With --replay, save the final comparison and exit without serving')
    args=parser.parse_args()
    dc.require(args.wad.exists(),'WAD missing; run scripts/fetch-shareware first.')
    dc.require(not args.check or args.replay is not None,'--check requires --replay commands.txt')
    print('Building live comparison workers…',flush=True)
    subprocess.run([str(ROOT/'scripts/lake'),'build','live-render-probe'],cwd=ROOT,check=True)
    if args.reference=='dos':
        import original_live_compare as original
        binary,key=original.build_reference(args.fetch)
        session=original.Session(args.wad,binary,key,args.out)
    else:
        binary,key=build_reference(args.fetch)
        session=Session(args.wad,binary,key,args.out)
    if args.replay:
        try:
            for line in args.replay.read_text().splitlines():
                if line.strip():session.step([int(n) for n in line.split()])
            print('Replay capture: '+session.save(),flush=True)
        except Exception:
            session.close();raise
    if args.check:
        session.close();return
    httpd=server(session,args.port)
    print(f'LIVE_COMPARISON_URL=http://127.0.0.1:{httpd.server_port}/',flush=True)
    print('E1M1 · same ticcmd to both engines · grayscale equality / red differences · Ctrl-C stops both workers',flush=True)
    try:httpd.serve_forever()
    except KeyboardInterrupt:pass
    finally:httpd.server_close();session.close()

if __name__=='__main__':main()

"""Independent audio oracles extracted from pinned Chocolate Doom/Nuked code."""
from pathlib import Path
import re
from motion_reference import function
ROOT=Path(__file__).resolve().parents[1]
CACHE=ROOT/'artifacts/reference/chocolate-doom-3.1.1'

def music_driver_source():
    s=(CACHE/'src/i_oplmusic.c').read_text()
    types=s[s.index('#define GENMIDI_NUM_INSTRS'):s.index('// Frequency values to use')]
    pre=r'''
#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>
typedef uint8_t byte;
typedef bool boolean;
typedef void midi_track_iter_t;
#define PACKED_STRUCT(x) struct __attribute__((packed)) x
#define SHORT(x) (x)
#define OPL_NUM_VOICES 9
#define MIDI_CHANNELS_PER_TRACK 16
#define OPL_REGS_LEVEL 0x40
#define OPL_REGS_TREMOLO 0x20
#define OPL_REGS_ATTACK 0x60
#define OPL_REGS_SUSTAIN 0x80
#define OPL_REGS_WAVEFORM 0xe0
#define OPL_REGS_FEEDBACK 0xc0
#define OPL_REGS_FREQ_1 0xa0
#define OPL_REGS_FREQ_2 0xb0
#define MIDI_CONTROLLER_VOLUME_MSB 7
#define MIDI_CONTROLLER_PAN 10
#define MIDI_CONTROLLER_ALL_NOTES_OFF 123
#define opl_doom1_1_666 0
#define opl_doom2_1_666 1
#define opl_doom_1_9 2
typedef struct { struct {struct {unsigned channel,param1,param2;} channel;} data;} midi_event_t;
static FILE *output;static int writes;
static void OPL_WriteRegister(unsigned r,unsigned v){if(writes++)fputc(' ',output);fprintf(output,"%u:%u",r,v&255);}
'''
    tables=s[s.index('static const unsigned short frequency_curve'):s.index('static opl_driver_ver_t')]
    globals=r'''
static genmidi_instr_t *main_instrs,*percussion_instrs;
static opl_voice_t voices[18],*voice_free_list[18],*voice_alloced_list[18];
static int voice_free_num,voice_alloced_num,num_opl_voices=9,opl_opl3mode=0,opl_drv_ver=2;
static int current_music_volume=64,start_music_volume=64;
static opl_channel_data_t channels[16];
static uint8_t last_perc[16];static unsigned last_perc_count;
static bool opl_stereo_correct;
static void VoiceKeyOff(opl_voice_t *voice);
'''
    code=''
    names=['GetFreeVoice','VoiceKeyOff','ReleaseVoice','LoadOperatorData','SetVoiceInstrument','SetVoiceVolume','SetVoicePan','InitVoices','TrackChannelForEvent','KeyOffEvent','ReplaceExistingVoice','ReplaceExistingVoiceDoom1','ReplaceExistingVoiceDoom2','FrequencyForVoice','UpdateVoiceFrequency','VoiceKeyOn','KeyOnEvent','ProgramChangeEvent','SetChannelVolume','SetChannelPan','AllNotesOff','ControllerEvent','PitchBendEvent','InitChannel']
    for name in names:
        # Find the definition rather than an earlier forward declaration.
        match=re.search(r'static [^;{}]+\b'+name+r'\([^;{}]*\)\s*\{',s)
        code+=function(s[match.start():],match.group().rstrip('{').rstrip())
    driver=r'''
int main(int argc,char **argv){
 if(argc!=4)return 2;FILE *bank=fopen(argv[1],"rb"),*in=fopen(argv[2],"r");output=fopen(argv[3],"w");if(!bank||!in||!output)return 2;
 char header[8];if(fread(header,1,8,bank)!=8)return 3;
 main_instrs=calloc(175,sizeof(genmidi_instr_t));if(fread(main_instrs,sizeof(genmidi_instr_t),175,bank)!=175)return 3;
 percussion_instrs=main_instrs+128;InitVoices();for(int i=0;i<16;i++)InitChannel(channels+i);
 unsigned status,a,b;opl_track_data_t track={0};
 while(fscanf(in,"%u %u %u",&status,&a,&b)==3){writes=0;midi_event_t e={.data.channel={status&15,a,b}};
 switch(status&0xf0){case 0x80:KeyOffEvent(&track,&e);break;case 0x90:KeyOnEvent(&track,&e);break;case 0xb0:ControllerEvent(&track,&e);break;case 0xc0:ProgramChangeEvent(&track,&e);break;case 0xe0:PitchBendEvent(&track,&e);break;default:abort();}fputc('\n',output);
 }
 free(main_instrs);fclose(in);fclose(output);fclose(bank);return 0;
}
'''
    return pre+types+tables+globals+code+driver

def mus_source():
    s=(CACHE/'src/mus2mid.c').read_text()
    s=re.sub(r'^#include.*$','',s,flags=re.M)
    pre=r'''
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <limits.h>
#include <stdbool.h>
typedef unsigned char byte;
typedef bool boolean;
#define PACKED_STRUCT(x) struct __attribute__((packed)) x
#define SHORT(x) (x)
#define CHECK_MUS_HEADER
#define MEMFILE FILE
#define mem_fread fread
#define mem_fwrite fwrite
#define mem_fseek fseek
#define MEM_SEEK_SET SEEK_SET
'''
    return pre+s+r'''
int main(int argc,char **argv){if(argc!=3)return 2;FILE *in=fopen(argv[1],"rb"),*out=fopen(argv[2],"wb");if(!in||!out)return 2;int result=mus2mid(in,out);fclose(in);fclose(out);return result;}
'''

def spatial_source():
    fixed=(CACHE/'src/m_fixed.c').read_text();fixed=fixed[fixed.index('fixed_t\nFixedMul'):]
    tables=(CACHE/'src/tables.c').read_text();tables=tables[tables.index('int SlopeDiv('):tables.index('const byte gammatable')]
    angle=(CACHE/'src/doom/r_main.c').read_text()
    code=function(angle,'angle_t\nR_PointToAngle\n')+function(angle,'angle_t\nR_PointToAngle2')
    sound=(CACHE/'src/doom/s_sound.c').read_text()
    return r'''
#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
typedef int fixed_t;typedef unsigned angle_t;
typedef struct {fixed_t x,y;angle_t angle;} mobj_t;
#define FINEANGLES 8192
#define FRACBITS 16
#define FRACUNIT 65536
#define ANGLETOFINESHIFT 19
#define SLOPERANGE 2048
#define S_CLIPPING_DIST (1200*FRACUNIT)
#define S_CLOSE_DIST (200*FRACUNIT)
#define S_ATTENUATOR 1000
#define S_STEREO_SWING (96*FRACUNIT)
#define ANG90 0x40000000
#define ANG180 0x80000000
#define ANG270 0xc0000000
fixed_t viewx,viewy;static int gamemap=1,snd_SfxVolume;
'''+fixed+tables+code+function(sound,'static int S_AdjustSoundParams')+r'''
int main(int argc,char **argv){if(argc!=3)return 2;FILE *in=fopen(argv[1],"r"),*out=fopen(argv[2],"w");if(!in||!out)return 2;
mobj_t listener,source;int map8;
while(fscanf(in,"%d %d %u %d %d %d %d",&listener.x,&listener.y,&listener.angle,&source.x,&source.y,&snd_SfxVolume,&map8)==7){gamemap=map8?8:1;int vol=snd_SfxVolume,sep=128;if(S_AdjustSoundParams(&listener,&source,&vol,&sep))fprintf(out,"%d %d\n",vol,sep);else fputs("none\n",out);}fclose(in);fclose(out);return 0;}
'''

def midi_events(data):
    import struct
    assert data[:4]==b'MThd' and data[14:18]==b'MTrk'
    end=22+struct.unpack_from('>I',data,18)[0];pos=22;time=0;events=[]
    def vlq():
        nonlocal pos
        n=0
        while True:
            b=data[pos];pos+=1;n=n*128+(b&127)
            if not b&128:return n
    while pos<end:
        time+=vlq();status=data[pos];pos+=1
        if status==255:
            kind=data[pos];pos+=1;n=vlq();pos+=n
            if kind==47:return dict(duration=time,events=events)
        else:
            a=data[pos];pos+=1;b=0
            if status&240 not in (192,208):b=data[pos];pos+=1
            events.append([time,status,a,b])
    raise AssertionError('no MIDI end marker')

def corpus():
    import random,struct
    r=random.Random(4919)
    # A complete bounded instrument bank: independent fixture encoding, including
    # fixed-note/double voices, extreme signed offsets and all four waveforms.
    bank=bytearray(b'#OPL_II#')
    for i in range(175):
        bank+=struct.pack('<HBB',[0,1,4,5][i%4],r.randrange(256),r.randrange(128))
        for _ in range(2):
            op=lambda:bytes([r.randrange(256),r.randrange(256),r.randrange(256),r.randrange(4),r.randrange(4)<<6,r.randrange(64)])
            bank+=op()+bytes([r.randrange(16)])+op()+b'\0'+struct.pack('<h',[-32768,-97,-12,0,12,96,32767][i%7])
    events=[]
    for i in range(128):
        c=i%16
        events += [f'{192+c} {i} 0',f'{176+c} 7 {r.randrange(128)}',f'{144+c} {r.randrange(128)} {r.randrange(1,128)}']
        if i%3==0:events+=[f'{224+c} {r.randrange(128)} {r.randrange(128)}']
        if i%7==0:events+=[f'{176+c} 123 0']
    for key in range(32,85):events += [f'153 {key} 100',f'137 {key} 0']
    for _ in range(2048):
        c=r.randrange(16);kind=r.choice([128,144,176,192,224])
        a=r.choice([7,10,120,121,123,64]) if kind==176 else r.randrange(128)
        events.append(f'{kind+c} {a} {r.randrange(128)}')
    opl=['s 128']
    for _ in range(12):
        opl.append(f'w 189 {r.choice([0,64,128,192])}')
        opl.append(f'w 8 {r.choice([0,64])}')
        for c,op in enumerate([0,1,2,8,9,10,16,17,18]):
            for slot in [op,op+3]:
                for reg,v in [(32,r.randrange(256)),(64,r.randrange(128)),(96,r.randrange(256)),(128,r.randrange(256)),(224,r.randrange(4))]:opl.append(f'w {reg+slot} {v}')
            opl += [f'w {192+c} {r.randrange(16)}',f'w {160+c} {r.randrange(256)}',f'w {176+c} {r.randrange(32)+32}']
        opl+=['s 10000']
        for c in range(9):opl.append(f'w {176+c} 0')
        opl+=['s 4000']
    spatial=[]
    for x,y in [(0,0),(199,0),(200,0),(201,0),(600,600),(1199,0),(1200,0),(1201,0),(-200,0),(0,200),(0,-200),(-900,-300)]:
        for angle in [0,1,0x20000000,0x40000000,0x80000000,0xffffffff]:
            for volume in [0,1,8,15,64,127]:
                for map8 in [0,1]:spatial.append(f'0 0 {angle} {x*65536} {y*65536} {volume} {map8}')
    for _ in range(2048):spatial.append(f'{r.randrange(-2000,2000)*65536} {r.randrange(-2000,2000)*65536} {r.randrange(2**32)} {r.randrange(-2000,2000)*65536} {r.randrange(-2000,2000)*65536} {r.randrange(128)} {r.randrange(2)}')
    # MUS uses explicit independent byte construction; exercise running velocity,
    # time VLQs, controller remapping, pitch and percussion channel allocation.
    score=bytes([0x40,0,30,0x90,0xbc,100,10,0x1f,0xa3,120,0xa0,144,0x81,0,0xb0,10,1,0xc1,3,80,5,0x80,60,10,0x9f,35,1,0x8f,35,10,0x60])
    mus=struct.pack('<4s6H',b'MUS\x1a',len(score),16,2,0,0,0)+score
    return bytes(bank),events,opl,spatial,mus

def channels_source():
    s=(CACHE/'src/doom/s_sound.c').read_text()
    base=spatial_source().split('int main(')[0]
    sounds=re.findall(r'\bSOUND\("(\w+)",\s*(\d+)\)',(CACHE/'src/doom/sounds.c').read_text())
    pre=r'''
#include <string.h>
#include <stdarg.h>
typedef struct sfxinfo_s {const char *name;int priority;struct sfxinfo_s *link;int pitch,volume,usefulness,lumpnum;} sfxinfo_t;
typedef struct {sfxinfo_t *sfxinfo;mobj_t *origin;int pitch,handle;} channel_t;
static channel_t channels[8];static int snd_channels=8;
static mobj_t origins[32];static struct {mobj_t *mo;} players[1];static int consoleplayer;
static int vols[8],seps[8];
#define NORM_PITCH 128
#define NORM_SEP 128
static int I_SoundIsPlaying(int h){(void)h;return 1;}
static void I_StopSound(int h){(void)h;}
static int I_GetSfxLumpNum(sfxinfo_t *s){(void)s;return 0;}
static int I_StartSound(sfxinfo_t *s,int c,int v,int sep,int pitch){(void)s;(void)pitch;vols[c]=v;seps[c]=sep;return c;}
static void I_Error(const char *m,...){(void)m;abort();}
'''
    pre+='static sfxinfo_t S_sfx[]={'+','.join('{"'+n+'",'+p+',NULL,128,0,0,-1}' for n,p in sounds)+'};\n'
    pre+=f'#define NUMSFX {len(sounds)-1}\n'
    for name in ['sawup','sawhit','itemup','tink']:pre+=f'#define sfx_{name} '+str(next(i for i,(n,_) in enumerate(sounds) if n==name))+'\n'
    random=(CACHE/'src/doom/m_random.c').read_text();a=random.index('const unsigned char rndtable');pre+=random[a:random.index('};',a)+2]+'\nstatic int rndindex;\n'+function(random,'int M_Random')
    code=''.join(function(s,sig) for sig in ['static void S_StopChannel','void S_StopSound','static int S_GetChannel','static int Clamp','void S_StartSound'])
    driver=r'''
int main(int argc,char **argv){if(argc!=3)return 2;FILE *in=fopen(argv[1],"r"),*out=fopen(argv[2],"w");if(!in||!out)return 2;players[0].mo=&origins[0];snd_SfxVolume=64;
char op[16],name[32];int id,x,y;unsigned angle;
while(fscanf(in,"%15s",op)==1){
 if(!strcmp(op,"reset")){if(fscanf(in,"%d %d",&rndindex,&snd_SfxVolume)!=2)return 3;memset(channels,0,sizeof(channels));}
 else if(!strcmp(op,"start")){if(fscanf(in,"%31s %d %d %d %u",name,&id,&x,&y,&angle)!=5)return 3;
  origins[0]=(mobj_t){0,0,angle};if(id>0)origins[id]=(mobj_t){x,y,0};int sfx=0;for(int i=1;i<=NUMSFX;i++)if(!strcmp(name,S_sfx[i].name))sfx=i;if(!sfx)return 4;
  S_StartSound(id<0?NULL:origins+id,sfx);
 }else return 3;
 fprintf(out,"%d|",rndindex);for(int i=0;i<8;i++){if(i)fputc(';',out);if(!channels[i].sfxinfo)fputc('-',out);else fprintf(out,"%s:%d:%d:%d:%d",channels[i].sfxinfo->name,channels[i].origin?(int)(channels[i].origin-origins):-1,channels[i].pitch,vols[i],seps[i]);}fputc('\n',out);
}fclose(in);fclose(out);return 0;}
'''
    return base+pre+code+driver

def channel_corpus():
    import random
    r=random.Random(741);out=[]
    names=['pistol','shotgn','itemup','tink','sawup','sawhit','doropn','stnmov','plpain','barexp','bgsit1','firsht','pldeth']
    for seed in range(0,256,17):
        out.append(f'reset {seed} 64')
        for _ in range(160):
            name=r.choice(names);origin=r.randrange(-1,24);x=r.choice([0,100,600,1199,1200,1500])*65536;y=r.choice([0,100,-300])*65536
            out.append(f'start {name} {origin} {x} {y} {r.randrange(2**32)}')
    return out


def main():
    import argparse,subprocess,tempfile,json,hashlib
    parser=argparse.ArgumentParser();parser.add_argument('--record',action='store_true');parser.add_argument('--fetch',action='store_true');args=parser.parse_args()
    manifest=ROOT/'tests/reference/audio.json'
    files=['src/doom/s_sound.c','src/doom/sounds.c','src/doom/sounds.h','src/i_oplmusic.c','src/i_sdlsound.c','src/mus2mid.c','src/mus2mid.h','opl/opl3.c','opl/opl3.h','src/m_fixed.c','src/tables.c','src/doom/r_main.c','src/doom/m_random.c']
    digest=lambda data:hashlib.sha256(data).hexdigest()
    spec=json.loads(manifest.read_text()) if manifest.exists() else None
    if args.fetch:
        import urllib.request
        if spec is None:raise RuntimeError('fetch requires a pinned audio manifest')
        for name,checksum in spec['files'].items():
            p=CACHE/name
            if not p.exists():
                data=urllib.request.urlopen('https://raw.githubusercontent.com/chocolate-doom/chocolate-doom/'+spec['commit']+'/'+name,timeout=30).read()
                assert digest(data)==checksum,name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    checksums={name:digest((CACHE/name).read_bytes()) for name in files}
    if spec is not None:
        for name,checksum in spec['files'].items():assert checksums[name]==checksum,'audio reference source changed: '+name
    bank,events,opl,spatial,mus=corpus()
    results={}
    with tempfile.TemporaryDirectory(prefix='lean-doom-audio-') as tmp:
        d=Path(tmp);(d/'bank').write_bytes(bank);(d/'mus').write_bytes(mus)
        for n,lines in [('driver',events),('opl',opl),('spatial',spatial),('channels',channel_corpus())]: (d/n).write_text('\n'.join(lines)+'\n')
        for name,source,inputs in [('driver',music_driver_source(),[d/'bank',d/'driver']),('mus',mus_source(),[d/'mus']),('spatial',spatial_source(),[d/'spatial']),('channels',channels_source(),[d/'channels']),('opl',(ROOT/'tests/reference/opl_fixture.c').read_text(),[d/'opl'])]:
            c=d/(name+'.c');c.write_text(source)
            outs=[]
            for opt in ['-O0','-O2']:
                binary=d/(name+opt)
                extra=['-I'+str(CACHE/'opl'),str(CACHE/'opl/opl3.c')] if name=='opl' else []
                subprocess.run(['cc','-std=c11',opt,'-fwrapv',*extra,str(c),'-o',str(binary)],check=True)
                out=d/(name+opt+'.out');subprocess.run([str(binary),*map(str,inputs),str(out)],check=True)
                raw=out.read_bytes()
                if name=='mus':raw=json.dumps(midi_events(raw),sort_keys=True).encode()
                outs.append(raw)
            assert outs[0]==outs[1],name+' optimizer mismatch'
            out=d/(name+'-lean.out');subprocess.run([str(ROOT/'.lake/build/bin/audio-probe'),name,*map(str,inputs),str(out)],check=True)
            raw=out.read_bytes()
            if name=='mus':raw=json.dumps(json.loads(raw),sort_keys=True).encode()
            assert raw==outs[0],(name,'C/Lean mismatch',next((i for i,(a,b) in enumerate(zip(raw,outs[0])) if a!=b),min(len(raw),len(outs[0]))))
            results[name]={'sha256':digest(raw),'bytes':len(raw)}
            print(name,'C -O0/-O2 and Lean agree:',len(raw),'bytes',flush=True)
    report={'commit':'410d96855b5df5410ff591a90efeafa889119224','files':checksums,'results':results,'harness_sha256':digest((music_driver_source()+mus_source()+spatial_source()+channels_source()+(ROOT/'tests/reference/opl_fixture.c').read_text()).encode()),'profile':'DOOM 1.9 OPL2 nine melodic voices; immediate writes, Nuked 1.8 44100-Hz resampler. SFX spatialization uses original map-8 exception. MUS valid-input event parity; strict malformed input rejection is separate. PCM output is not a DOS hardware recording.'}
    if args.record:manifest.write_text(json.dumps(report,indent=2)+'\n')
    else:assert spec==report,'audio oracle outputs changed; inspect and explicitly record'

if __name__=='__main__':main()

"""Original renderer arithmetic extracted from hash-pinned C, without Lean calls."""
import json
from pathlib import Path
import subprocess
import tarfile
import fidelity_reference as ref
from motion_reference import function

ROOT=Path(__file__).resolve().parents[1]


def source():
    s=ref.sources()
    spec=json.loads((ROOT/'tests/reference/tick-trace.json').read_text())
    archive=ROOT/'artifacts/reference/chocolate-doom-3.1.1-full.tar.gz'
    if ref.digest(archive.read_bytes())!=spec['archive_sha256']:raise ValueError('renderer source archive hash mismatch')
    with tarfile.open(archive) as t:
        bsp=t.extractfile(f'chocolate-doom-{spec["commit"]}/src/doom/r_bsp.c').read().decode()
    tables=s['src/tables.c'];tables=tables[tables.index('const fixed_t finetangent[4096]'):]
    tables=tables[:tables.rfind('};')+2]
    main=s['src/doom/r_main.c'];segs=s['src/doom/r_segs.c'];planes=s['src/doom/r_plane.c']
    fixed=s['src/m_fixed.c'];div=function(fixed,'fixed_t FixedDiv')
    if 'FixedDiv2' in div:div=function(fixed,'fixed_t FixedDiv2')+'\n'+div
    # Stop before R_AddLine's sector classification. This prefix is unchanged.
    add=function(bsp,'void R_AddLine')
    add=add[:add.index('    backsector = line->backsector;')]+ '\n resultFirst=x1;resultStop=x2;\n}\n'
    wall=function(segs,'void\nR_StoreWallRange')
    distance=wall[wall.index('    // calculate rw_distance'):wall.index('    ds_p->x1')]
    offset=wall[wall.index('\toffsetangle = rw_normalangle-rw_angle1;'):wall.index('\t// calculate light table')]
    # Use R_MapPlane unchanged, replacing only its drawing callback with an observer.
    mapplane=function(planes,'void\nR_MapPlane')
    initview=function(main,'void R_ExecuteSetViewSize')
    initplanes=initview[initview.index('    // planes'):initview.index('    // Calculate the light levels')]
    clear=function(planes,'void R_ClearPlanes')
    base=clear[clear.index('    // left to right mapping'):clear.rfind('}')]
    return r'''
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
typedef uint8_t byte;typedef uint8_t pixel_t;typedef int32_t fixed_t;typedef uint32_t angle_t;
#define FRACBITS 16
#define FRACUNIT 65536
#define FINEANGLES 8192
#define FIELDOFVIEW 2048
#define ANGLETOFINESHIFT 19
#define ANG90 0x40000000u
#define ANG180 0x80000000u
#define ANG270 0xc0000000u
#define DBITS 5
#define SLOPERANGE 2048
#define LIGHTZSHIFT 20
#define MAXLIGHTZ 128
static int centerx=160,centerxfrac=160*65536,viewwidth=320,viewheight=168,detailshift;
static int viewangletox[4096];static angle_t xtoviewangle[321],clipangle;
static fixed_t viewx,viewy,projection=160*65536,rw_distance,rw_offset;
static angle_t viewangle,rw_normalangle,rw_angle1,rw_centerangle;
typedef struct {fixed_t x,y;} vertex_t;
typedef struct {vertex_t *v1,*v2;angle_t angle;fixed_t offset;} seg_t;
static seg_t *curline;
static struct {fixed_t textureoffset;} side,*sidedef=&side;
static int resultFirst,resultStop;
static fixed_t planeheight,basexscale,baseyscale,yslope[200],distscale[320];
static fixed_t cachedheight[200],cacheddistance[200],cachedxstep[200],cachedystep[200];
static fixed_t ds_xstep,ds_ystep,ds_xfrac,ds_yfrac;
static byte *fixedcolormap,*ds_colormap,*planezlight[128];
static int ds_y,ds_x1,ds_x2;
static byte flat[4096],*ds_source=flat;
static void spanfunc(void){}
static byte screen[64000],sourceColumn[128],identity[256],*ylookup[200];
static int columnofs[320],dc_x,dc_yl,dc_yh,centery;
static fixed_t dc_iscale,dc_texturemid;
static byte *dc_source=sourceColumn,*dc_colormap=identity;
#define SCREENWIDTH 320
'''+function(fixed,'fixed_t\nFixedMul')+'\n'+div+'\n'+tables+'\n'+r'''
#define finecosine (finesine+2048)
'''+function(s['src/tables.c'],'int SlopeDiv')+'\n'+function(main,'angle_t\nR_PointToAngle')+'\n'+function(main,'fixed_t\nR_PointToDist')+'\n'+function(main,'fixed_t R_ScaleFromGlobalAngle')+'\n'+function(main,'void R_InitTextureMapping')+'\n'+add+'\n'+mapplane+'\n'+function(s['src/doom/r_draw.c'],'void R_DrawColumn')+'\n'+function(s['src/doom/r_draw.c'],'void R_DrawSpan')+'\n'+r'''
int main(void){R_InitTextureMapping();char op[32];int32_t a,b,c,d,e,f,g;
while(scanf("%31s %d %d %d %d %d %d %d",op,&a,&b,&c,&d,&e,&f,&g)==8){
if(!strcmp(op,"project")){
 viewx=viewy=0;viewangle=(uint32_t)a;
 vertex_t v1={b,c},v2={d,e};seg_t seg={&v1,&v2,(uint32_t)f,0};
 sidedef->textureoffset=g;resultFirst=resultStop=-1;R_AddLine(&seg);
 if(resultFirst<0){puts("hidden");continue;}
 fixed_t hyp,sineval;angle_t distangle,offsetangle;
'''+distance+offset+r'''
 int x1=resultFirst,x2=resultStop-1,xm=(x1+x2)/2;
 printf("%d %d %d %d %u %d %d %d %d %d\n",x1,x2+1,rw_distance,rw_offset,rw_centerangle,
 R_ScaleFromGlobalAngle(viewangle+xtoviewangle[x1]),R_ScaleFromGlobalAngle(viewangle+xtoviewangle[x2]),
 (rw_offset-FixedMul(finetangent[(rw_centerangle+xtoviewangle[x1])>>19],rw_distance))>>16,
 (rw_offset-FixedMul(finetangent[(rw_centerangle+xtoviewangle[xm])>>19],rw_distance))>>16,
 (rw_offset-FixedMul(finetangent[(rw_centerangle+xtoviewangle[x2])>>19],rw_distance))>>16);
}else if(!strcmp(op,"column")){
 viewx=viewy=0;viewangle=(uint32_t)a;
 vertex_t v1={b,c};seg_t seg={&v1,&v1,(uint32_t)d,0};curline=&seg;
 rw_angle1=R_PointToAngle(b,c);sidedef->textureoffset=e;
 fixed_t hyp,sineval;angle_t distangle,offsetangle;
'''+distance+offset+r'''
 printf("%d %d\n",(rw_offset-FixedMul(finetangent[(rw_centerangle+xtoviewangle[f])>>19],rw_distance))>>16,
 R_ScaleFromGlobalAngle(viewangle+xtoviewangle[f]));
}else if(!strcmp(op,"span")){
 for(int i=0;i<4096;i++)flat[i]=f ? i>>8 : i&255;
 for(int i=0;i<256;i++)identity[i]=i;
 ylookup[0]=screen;ds_colormap=identity;
 ds_xfrac=a;ds_yfrac=b;ds_xstep=c;ds_ystep=d;ds_y=0;ds_x1=0;ds_x2=e-1;
 R_DrawSpan();for(int i=0;i<e;i++)printf(i ? " %u" : "%u",screen[i]);puts("");
}else if(!strcmp(op,"wallpixel")){
 for(int i=0;i<128;i++)sourceColumn[i]=i;
 for(int i=0;i<256;i++)identity[i]=i;
 for(int i=0;i<200;i++)ylookup[i]=screen+320*i;
 centery=c/2;dc_iscale=0xffffffffu/(uint32_t)a;dc_texturemid=b;
 dc_x=0;dc_yl=dc_yh=d;R_DrawColumn();printf("%u\n",screen[d*320]);
}else if(!strcmp(op,"plane")){
 viewangle=(uint32_t)a;viewx=b;viewy=c;planeheight=d;viewheight=e;
 int i;fixed_t dy,cosadj;angle_t angle;
'''+initplanes+base+r'''
 memset(cachedheight,0,sizeof(cachedheight));R_MapPlane(f,g,g);
 printf("%d %d %d %d %d\n",cacheddistance[f],ds_xfrac,ds_yfrac,ds_xstep,ds_ystep);
}}
return 0;
}
'''


def build(directory,opt='-O2'):
    directory=Path(directory);p=directory/'projection.c';p.write_text(source())
    binary=directory/'projection'
    subprocess.run(['cc',opt,'-fwrapv',str(p),'-o',str(binary)],check=True,capture_output=True,text=True)
    return binary


from functools import cache
import tempfile
@cache
def fixture():
    directory=tempfile.TemporaryDirectory()
    return directory,build(directory.name)


def evaluate(commands):
    _,binary=fixture()
    return subprocess.run([str(binary)],input='\n'.join(commands)+'\n',text=True,capture_output=True,check=True).stdout.splitlines()

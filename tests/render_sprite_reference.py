"""Unchanged R_ProjectSprite/R_DrawMaskedColumn and animation update C bodies."""
from pathlib import Path
import subprocess
import render_projection_reference as projection
import fidelity_reference as ref
from motion_reference import function


def source():
    sources=ref.sources();things=sources['src/doom/r_things.c']
    spec=sources['src/doom/p_spec.c']
    update=function(spec,'void P_UpdateSpecials')
    update=update[update.index('    for (anim = anims'):update.index('    //\tANIMATE LINE SPECIALS')]
    return projection.source().split('int main(void)')[0]+r'''
#define MINZ (4*65536)
#define FF_FRAMEMASK 32767
#define FF_FULLBRIGHT 32768
#define MF_SHADOW 0x40000
#define LIGHTSCALESHIFT 12
#define MAXLIGHTSCALE 48
#define ANG45 0x20000000u
typedef int boolean;
typedef struct {fixed_t x,y,z;angle_t angle;int sprite,frame,flags;} mobj_t;
typedef struct {int rotate,lump[8],flip[8];} spriteframe_t;
typedef struct {int numframes;spriteframe_t *spriteframes;} spritedef_t;
typedef struct {fixed_t scale,gx,gy,gz,gzt,texturemid,startfrac,xiscale;int x1,x2,patch,mobjflags;byte *colormap;} vissprite_t;
static spriteframe_t frame;static spritedef_t sprites[1]={{1,&frame}};
static fixed_t viewsin,viewcos,viewz,spriteoffset[8],spritewidth[8],spritetopoffset[8];
static byte *spritelights[48],*colormaps=identity;
static vissprite_t output;static int found;
static vissprite_t *R_NewVisSprite(void){found=1;return &output;}
'''+function(things,'void R_ProjectSprite')+r'''
typedef struct {byte topdelta,length,unused;} column_t;
static short floorclip[320],ceilingclip[320],*mfloorclip=floorclip,*mceilingclip=ceilingclip;
static fixed_t spryscale,sprtopscreen;
static void colfunc(void){found=1;printf("%d %d %d\n",dc_yl,dc_yh,dc_texturemid);}
'''+function(things,'void R_DrawMaskedColumn')+r'''
typedef struct {int istexture,basepic,numpics,speed;} anim_t;
static anim_t anims[1],*lastanim=anims+1;
static int texturetranslation[2048],flattranslation[2048],leveltime;
int main(void){char op[32];int32_t a,b,c,d,e,f,g,h,j,k;
while(scanf("%31s",op)==1){
if(!strcmp(op,"sprite")){
 if(scanf("%d%d%d%d%d%d%d%d%d%d",&a,&b,&c,&d,&e,&f,&g,&h,&j,&k)!=10)return 2;
 viewx=viewy=0;viewangle=a;viewsin=finesine[viewangle>>19];viewcos=finecosine[viewangle>>19];viewz=e;
 for(int i=0;i<8;i++){spritewidth[i]=f*65536;spriteoffset[i]=g*65536;spritetopoffset[i]=h*65536;frame.lump[i]=i;frame.flip[i]=j;}
 frame.rotate=1;mobj_t thing={b,c,d,(uint32_t)k,0,0,0};found=0;R_ProjectSprite(&thing);
 if(!found||output.x1>output.x2)puts("hidden");else printf("%d %d %d %d %d %d %d\n",output.patch,output.scale,output.x1,output.x2+1,output.startfrac,output.xiscale,output.texturemid);
}else if(!strcmp(op,"post")){
 if(scanf("%d%d%d%d%d%d%d",&a,&b,&c,&d,&e,&f,&g)!=7)return 2;
 byte column[300]={0};column[0]=d;column[1]=e;column[e+4]=255;
 dc_x=0;dc_texturemid=b;spryscale=a;sprtopscreen=(c/2)*65536-FixedMul(b,a);
 ceilingclip[0]=f;floorclip[0]=g;found=0;R_DrawMaskedColumn((column_t*)column);if(!found)puts("hidden");
}else if(!strcmp(op,"anim")){
 if(scanf("%d%d%d%d",&a,&b,&c,&d)!=4)return 2;
 for(int i=0;i<2048;i++)texturetranslation[i]=flattranslation[i]=i;
 anims[0]=(anim_t){1,b,c,8};leveltime=a-1;int i,pic;anim_t *anim;
 if(a){
'''+update+r'''
 }printf("%d\n",texturetranslation[d]);
}else return 2;
}return 0;}
'''


def build(directory,opt):
    p=Path(directory)/'sprite.c';p.write_text(source());binary=p.with_suffix('')
    subprocess.run(['cc',opt,'-fwrapv',str(p),'-o',str(binary)],text=True,capture_output=True,check=True)
    return binary

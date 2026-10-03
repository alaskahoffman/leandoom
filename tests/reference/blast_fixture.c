#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
typedef int fixed_t; typedef int boolean;
#define FRACBITS 16
#define MAXRADIUS (32<<16)
#define MAPBLOCKSHIFT 23
#define MF_SHOOTABLE 4
#define MT_CYBORG 16
#define MT_SPIDER 7
#define ML_TWOSIDED 4
#define NF_SUBSECTOR 32768
#define PT_EARLYOUT 4
#define PT_ADDLINES 1
#define exe_doom_1_2 2
#define LINKED_LIST_CHECK_NO_CYCLE(type,first,next) ((void)0)
typedef struct {fixed_t x,y,dx,dy;} divline_t;
typedef struct {fixed_t x,y;} vertex_t;
typedef struct {fixed_t floorheight,ceilingheight;} sector_t;
typedef struct {vertex_t *v1,*v2;int flags,validcount;sector_t *frontsector,*backsector;} line_t;
typedef struct {line_t *linedef;sector_t *frontsector,*backsector;} seg_t;
typedef struct {int numlines,firstline;sector_t *sector;} subsector_t;
typedef struct {fixed_t x,y,dx,dy;unsigned short children[2];} node_t;
typedef struct mobj_s {fixed_t x,y,z,height,radius;int flags,type;subsector_t *subsector;struct mobj_s *bnext;} mobj_t;
static sector_t sectors[2];static line_t lines[1];static seg_t segs[2];static subsector_t subsectors[2];static node_t nodes[1];
static int numsectors=2,numnodes=1,validcount,gameversion=9,sightcounts[2];
static unsigned char rejects[1],*rejectmatrix=rejects;
static fixed_t sightzstart,topslope,bottomslope,t2x,t2y;
static divline_t strace;
static mobj_t *bombspot,*bombsource;static int bombdamage;
static fixed_t bmaporgx,bmaporgy;static int bmapwidth=4,bmapheight=4;
static mobj_t *blocklinks[16],things[32];
static int amount,sight_calls,visible,blast_mode;
static char trace[1024];
static boolean PTR_SightTraverse(void *p){(void)p;abort();}
static boolean P_PathTraverse(int a,int b,int c,int d,int flags,boolean(*fn)(void *)){(void)a;(void)b;(void)c;(void)d;(void)flags;(void)fn;abort();}
static void P_DamageMobj(mobj_t *t,mobj_t *spot,mobj_t *source,int n){(void)spot;(void)source;amount=n;if(blast_mode){char part[40];snprintf(part,sizeof(part)," %td:%d",t-things,n);strcat(trace,part);}}
static boolean radius_sight(mobj_t *a,mobj_t *b){(void)b;sight_calls++;return blast_mode?(a-things)%3!=0:visible;}
/* ROUTINES */
static int next(void){char *p=strtok(NULL," \r\n");assert(p);return (int)strtol(p,NULL,10);}
int main(int argc,char **argv){
    assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char buf[1024];
    while(fgets(buf,sizeof(buf),f)){
        char *op=strtok(buf," \r\n");if(!op)continue;
        if(!strcmp(op,"side")){
            int x=next(),y=next();divline_t line;line.x=next();line.y=next();line.dx=next();line.dy=next();printf("%d\n",P_DivlineSide(x,y,&line));
        }else if(!strcmp(op,"falloff")){
            mobj_t a={0},b={0};a.x=next();a.y=next();b.x=next();b.y=next();b.radius=next();b.flags=next();b.type=next();bombdamage=next();visible=next();
            bombspot=&a;bombsource=NULL;amount=sight_calls=blast_mode=0;PIT_RadiusAttack(&b);printf("%d %d\n",amount,sight_calls);
        }else if(!strcmp(op,"portal")){
            int v[15];for(int i=0;i<15;i++)v[i]=next();
            vertex_t a=v[14]?(vertex_t){-128*65536,64*65536}:(vertex_t){64*65536,-128*65536};
            vertex_t b=v[14]?(vertex_t){128*65536,64*65536}:(vertex_t){64*65536,128*65536};
            sectors[0]=(sector_t){v[8]*65536,v[9]*65536};sectors[1]=(sector_t){v[10]*65536,v[11]*65536};
            lines[0]=(line_t){&a,&b,v[12],0,&sectors[0],&sectors[1]};
            segs[0]=(seg_t){lines,&sectors[0],&sectors[1]};segs[1]=(seg_t){lines,&sectors[1],&sectors[0]};
            subsectors[0]=(subsector_t){1,0,&sectors[0]};subsectors[1]=(subsector_t){1,1,&sectors[1]};
            nodes[0]=(node_t){a.x,a.y,b.x-a.x,b.y-a.y,{NF_SUBSECTOR,NF_SUBSECTOR|1}};
            rejects[0]=v[13];validcount=0;
            mobj_t looker={.x=v[0]*65536,.y=v[1]*65536,.z=v[2]*65536,.height=v[3]*65536,.subsector=&subsectors[0]};
            mobj_t target={.x=v[4]*65536,.y=v[5]*65536,.z=v[6]*65536,.height=v[7]*65536,.subsector=&subsectors[1]};
            printf("%d\n",P_CheckSight(&looker,&target));
        }else if(!strcmp(op,"blast")){
            bmaporgx=next();bmaporgy=next();mobj_t spot={0};spot.x=next();spot.y=next();int damage=next();
            memset(blocklinks,0,sizeof(blocklinks));memset(things,0,sizeof(things));trace[0]=0;blast_mode=1;
            for(int i=0;i<32;i++){
                int cell=i%16;mobj_t *t=&things[i];
                t->x=bmaporgx+((cell%4)*128+60+i%2)*65536;t->y=bmaporgy+((cell/4)*128+60)*65536;
                t->radius=(i%4)*8*65536;t->flags=i%5?4:0;t->type=i%7?3001:16;
                t->bnext=blocklinks[cell];blocklinks[cell]=t;
            }
            P_RadiusAttack(&spot,NULL,damage);printf("hits%s\n",trace);
        }else abort();
    }fclose(f);return 0;
}

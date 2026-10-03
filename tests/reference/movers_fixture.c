/* Selected E1M1 mover domains. Unchanged original routines and source blocks.
 * Plane obstruction supplied by the fixture; real clipping tested separately.
 * Allocation is zeroed for deterministic unused fields; no dependency on an
 * uninitialized spawn countdown is asserted. GPL-2.0-or-later. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <assert.h>
#include <stdbool.h>
typedef int fixed_t;
typedef int boolean;
typedef void(*actionf_p1)(void*);
typedef struct {struct {actionf_p1 acp1;} function;int removed;} thinker_t;
typedef struct sector_s sector_t;
typedef struct {int flags;short special,tag;sector_t *frontsector,*backsector;} line_t;
struct sector_s {fixed_t floorheight,ceilingheight;void *specialdata;int soundorg,special,floorpic,linecount;short tag;line_t *lines[64];};
typedef struct {void *player;int type;} mobj_t;
#define FRACUNIT 65536
#define TICRATE 35
#define ML_TWOSIDED 4
#define PU_LEVSPEC 0
#define exe_doom_1_2 0
static const int gameversion=1;
enum {sfx_stnmov,sfx_pstop,sfx_pstart};
enum {MT_ROCKET=1,MT_PLASMA,MT_BFG,MT_TROOPSHOT,MT_HEADSHOT,MT_BRUISERSHOT};
/* TYPES */
static sector_t sectors[64],solo_sector;
static line_t lines[64];
static int numsectors,numlines,leveltime;
static thinker_t *thinkers[256];static int nth;
static plat_t *activeplats[MAXPLATS],solo_plat;
static floormove_t solo_floor;
static unsigned replies,calls;
static char trace[8192];static size_t used;
static void event(const char *format,...) {va_list args;va_start(args,format);int n=vsnprintf(trace+used,sizeof(trace)-used,format,args);va_end(args);assert(n>=0&&(size_t)n<sizeof(trace)-used);used+=n;}
static void I_Error(const char *s,...) {(void)s;abort();}
static void clear_trace(unsigned mask) {replies=mask;calls=0;used=0;trace[0]=0;}
static void *Z_Malloc(size_t n,int tag,void *p) {(void)tag;(void)p;void *r=calloc(1,n);assert(r);return r;}
static void P_AddThinker(thinker_t *t) {assert(nth<256);thinkers[nth++]=t;}
static void P_RemoveThinker(thinker_t *t) {t->removed=1;event(" r");}
static void S_StartSound(void *origin,int sound) {(void)origin;event(" s %d",sound);}
static boolean P_ChangeSector(sector_t *s,boolean crush) {assert(!crush && calls<32);event(" c %d %d",s->floorheight,s->ceilingheight);return (replies>>calls++)&1;}
static void P_AddActivePlat(plat_t *p);
static void P_RemoveActivePlat(plat_t *p);
/* ROUTINES */
static int EV_DoFloor(line_t *line,floor_e floortype) {
    int secnum,rtn;sector_t *sec;floormove_t *floor;
/* FLOOR_SPAWN */
}
static int EV_DoPlat(line_t *line,plattype_e type,int amount) {
    int secnum,rtn;sector_t *sec;plat_t *plat;(void)amount;
/* PLAT_SPAWN */
}
static void cross_line(int linenum,int player,int projectile,int side) {
    line_t *line;int ok;mobj_t object={player?&object:NULL,projectile?MT_ROCKET:0};mobj_t *thing=&object;(void)side;
/* CROSS_GATE */
    switch(line->special) {
/* CROSS_CASES */
    }
}
static void dump_world(void) {
    printf("%d",numsectors);for(int i=0;i<numsectors;i++)printf(" %d %d",sectors[i].floorheight,sectors[i].specialdata!=NULL);
    printf(" | %d",numlines);for(int i=0;i<numlines;i++)printf(" %d",lines[i].special);
    int n=0;for(int i=0;i<nth;i++)if(!thinkers[i]->removed)n++;
    printf(" | %d",n);
    for(int i=0;i<nth;i++)if(!thinkers[i]->removed) {
        if(thinkers[i]->function.acp1==(actionf_p1)T_MoveFloor) {floormove_t *f=(void*)thinkers[i];printf(" %td 0 %d 0 %d 1 0 105",f->sector-sectors,f->floordestheight,f->speed);}
        else {plat_t *p=(void*)thinkers[i];printf(" %td 1 %d %d %d %d %d %d",p->sector-sectors,p->low,p->high,p->speed,p->status,p->count,p->wait);}
    }
    printf(" /%s\n",trace);
}
static void dump_solo(int floor) {
    if(floor)printf("f %d %d %d /%s\n",solo_sector.floorheight,solo_sector.ceilingheight,solo_floor.thinker.removed,trace);
    else printf("p %d %d %d %d %d /%s\n",solo_sector.floorheight,solo_sector.ceilingheight,solo_plat.status,solo_plat.count,solo_plat.thinker.removed,trace);
}
static void reset_world(void) {for(int i=0;i<nth;i++)free(thinkers[i]);nth=numlines=numsectors=0;memset(sectors,0,sizeof(sectors));memset(activeplats,0,sizeof(activeplats));}
int main(int argc,char **argv) {
    assert(argc==2);FILE *in=fopen(argv[1],"r");assert(in);char text[1024];
    while(fgets(text,sizeof(text),in)) {
        char *op=strtok(text," \n"),*p;int a[16],n=0;while((p=strtok(NULL," \n"))) {assert(n<16);a[n++]=(int)strtoll(p,NULL,10);}
        if(!strcmp(op,"floor")&&n==6) {
            solo_sector=(sector_t){.floorheight=a[0],.ceilingheight=a[1],.specialdata=&solo_floor};
            solo_floor=(floormove_t){.type=turboLower,.sector=&solo_sector,.direction=-1,.speed=a[3],.floordestheight=a[2]};leveltime=a[4];clear_trace(a[5]);T_MoveFloor(&solo_floor);dump_solo(1);
        } else if(!strcmp(op,"lift")&&n==10) {
            solo_sector=(sector_t){.floorheight=a[0],.ceilingheight=a[1],.specialdata=&solo_plat};
            solo_plat=(plat_t){.type=downWaitUpStay,.sector=&solo_sector,.low=a[2],.high=a[3],.speed=a[4],.status=a[5],.count=a[6],.wait=a[7]};
            memset(activeplats,0,sizeof(activeplats));activeplats[0]=&solo_plat;leveltime=a[8];clear_trace(a[9]);T_PlatRaise(&solo_plat);dump_solo(0);
        } else if(!strcmp(op,"lifttick")&&n==2) {leveltime=a[0];clear_trace(a[1]);if(!solo_plat.thinker.removed)T_PlatRaise(&solo_plat);dump_solo(0);}
        else if(!strcmp(op,"reset")&&n==0) {reset_world();puts("reset");}
        else if(!strcmp(op,"sector")&&n==4) {assert(numsectors<64);sector_t *s=&sectors[numsectors++];s->floorheight=(int)((unsigned)a[0]*65536u);s->ceilingheight=(int)((unsigned)a[1]*65536u);s->tag=a[2];s->specialdata=a[3]?(void*)1:NULL;puts("sector");}
        else if(!strcmp(op,"line")&&n==5) {
            assert(numlines<64&&a[1]>=0&&a[1]<numsectors&&a[2]<numsectors);line_t *l=&lines[numlines++];*l=(line_t){.flags=a[0],.special=a[3],.tag=a[4],.frontsector=&sectors[a[1]],.backsector=a[2]<0?NULL:&sectors[a[2]]};
            l->frontsector->lines[l->frontsector->linecount++]=l;
            if(l->backsector && l->backsector!=l->frontsector)l->backsector->lines[l->backsector->linecount++]=l;puts("line");
        } else if(!strcmp(op,"cross")&&n==4) {clear_trace(0);cross_line(a[0],a[1],a[2],a[3]);dump_world();}
        else if(!strcmp(op,"worldtick")&&n==1) {leveltime=a[0];clear_trace(0);for(int i=0;i<nth;i++)if(!thinkers[i]->removed) {calls=0;if(thinkers[i]->function.acp1==(actionf_p1)T_MoveFloor)T_MoveFloor((void*)thinkers[i]);else T_PlatRaise((void*)thinkers[i]);}dump_world();}
        else return 3;
    }
    reset_world();fclose(in);return 0;
}

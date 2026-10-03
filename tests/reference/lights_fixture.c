/* Minimal thinker/sector host for unchanged original lighting routines.
   Other sector-special handlers are outside this fixture. GPL-2.0-or-later. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#define ML_TWOSIDED 4
#define PU_LEVSPEC 0
#define exe_doom_1_2 0
static const int gameversion=1;
static int totalsecret;
typedef void (*actionf_p1)(void *);
typedef struct { struct { actionf_p1 acp1; } function; } thinker_t;
typedef struct sector_s sector_t;
typedef struct { int flags; sector_t *frontsector,*backsector; short special,tag; } line_t;
struct sector_s { short lightlevel,special,tag; void *specialdata; int linecount; line_t *lines[64]; };
typedef struct { void *player; } mobj_t;
static sector_t sectors[32];
static line_t lines[64];
static int numsectors,numlines;
static thinker_t *thinkers[32];static int nth;
static void *Z_Malloc(size_t size,int tag,void *user) { (void)tag;(void)user;void *p=calloc(1,size);assert(p);return p; }
static void P_AddThinker(thinker_t *t) { assert(nth<32);thinkers[nth++]=t; }
static void P_SpawnDoorCloseIn30(sector_t *s) { (void)s; }
static void P_SpawnDoorRaiseIn5Mins(sector_t *s,int i) { (void)s;(void)i; }
/* TYPES_CONSTANTS */
/* RANDOM */
/* ROUTINES */
static void cross_line(int index,int player,int side) {
    line_t *line=&lines[index];mobj_t object={player?&object:NULL};mobj_t *thing=&object;int ok;
    (void)side; // These original cases do not filter crossing direction.
/* CROSS_GATE */
    switch(line->special) {
/* CROSS_CASES */
    }
}
static void spawn_all(void) {
    sector_t *sector;int i;
/* SPAWN_SELECTION */
}
static void clear(void) { for(int i=0;i<nth;i++)free(thinkers[i]);nth=0;numsectors=0;numlines=0;totalsecret=0;memset(sectors,0,sizeof(sectors)); }
static void tick(void) {
    for(int i=0;i<nth;i++) {
        thinker_t *t=thinkers[i];
        if(t->function.acp1==(actionf_p1)T_FireFlicker)T_FireFlicker((fireflicker_t*)t);
        else if(t->function.acp1==(actionf_p1)T_LightFlash)T_LightFlash((lightflash_t*)t);
        else if(t->function.acp1==(actionf_p1)T_StrobeFlash)T_StrobeFlash((strobe_t*)t);
        else T_Glow((glow_t*)t);
    }
}
static void dump(void) {
    printf("%d %d",prndindex,rndindex);
    for(int i=0;i<numsectors;i++)printf(" | %d %d",sectors[i].lightlevel,sectors[i].special);
    printf(" / ");
    for(int i=0;i<nth;i++) {
        thinker_t *t=thinkers[i];sector_t *sec;int kind,count,min,max,dark=0,dir=0;
        if(t->function.acp1==(actionf_p1)T_FireFlicker) {fireflicker_t *f=(void*)t;kind=0;sec=f->sector;count=f->count;min=f->minlight;max=f->maxlight;}
        else if(t->function.acp1==(actionf_p1)T_LightFlash) {lightflash_t *f=(void*)t;kind=1;sec=f->sector;count=f->count;min=f->minlight;max=f->maxlight;}
        else if(t->function.acp1==(actionf_p1)T_StrobeFlash) {strobe_t *f=(void*)t;kind=2;sec=f->sector;count=f->count;min=f->minlight;max=f->maxlight;dark=f->darktime;}
        else {glow_t *f=(void*)t;kind=3;sec=f->sector;count=0;min=f->minlight;max=f->maxlight;dir=f->direction;}
        printf("| %ld %d %d %d %d %d %d ",sec-sectors,kind,count,min,max,dark,dir);
    }
    putchar('\n');
}
int main(int argc,char **argv) {
    assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char line[256],op[32];int a,b,c;
    while(fgets(line,sizeof(line),f)) {
        int n=sscanf(line,"%31s %d %d %d",op,&a,&b,&c);
        if(n==3&&!strcmp(op,"reset")) {clear();prndindex=a;rndindex=b;puts("reset");}
        else if(n==3&&!strcmp(op,"sector")) {assert(numsectors<32);sectors[numsectors].lightlevel=a;sectors[numsectors++].special=b;puts("sector");}
        else if(n==4&&!strcmp(op,"line")) {
            assert(numlines<64&&b>=0&&b<numsectors&&c<numsectors);
            line_t *l=&lines[numlines++];*l=(line_t){.flags=a,.frontsector=&sectors[b],.backsector=c<0?NULL:&sectors[c]};
            sectors[b].lines[sectors[b].linecount++]=l;
            if(c>=0&&c!=b)sectors[c].lines[sectors[c].linecount++]=l;
            puts("line");
        } else if(n==4&&!strcmp(op,"tagsector")) {assert(a>=0&&a<numsectors);sectors[a].tag=b;sectors[a].specialdata=c?&sectors[a]:NULL;puts("tagsector");}
        else if(n==4&&!strcmp(op,"trigger")) {assert(a>=0&&a<numlines);lines[a].special=b;lines[a].tag=c;puts("trigger");}
        else if(n==4&&!strcmp(op,"cross")) {assert(a>=0&&a<numlines);cross_line(a,b,c);printf("special %d ",lines[a].special);dump();}
        else if(n==1&&!strcmp(op,"spawn")) {spawn_all();dump();}
        else if(n==1&&!strcmp(op,"tick")) {tick();dump();}
        else if(n==3&&!strcmp(op,"set")) {assert(a>=0&&a<numsectors);sectors[a].lightlevel=b;dump();}
        else if(n==2&&!strcmp(op,"play")) {for(int i=0;i<a;i++)P_Random();dump();}
        else if(n==2&&!strcmp(op,"misc")) {for(int i=0;i<a;i++)M_Random();dump();}
        else abort();
    }
    clear();fclose(f);return 0;
}

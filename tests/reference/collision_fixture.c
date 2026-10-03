/* Test-only bounded scene. All things are solid/inert, and the mover is a
 * player without pickup/missile/skull effects. Unsupported effects abort. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
typedef int fixed_t;
typedef int boolean;
_Static_assert(sizeof(int)==4 && sizeof(short)==2 && CHAR_BIT==8, "widths");
_Static_assert((-1>>1)==-1 && (int32_t)UINT32_MAX==-1, "signed profile");
#define FRACBITS 16
#define FRACUNIT 65536
#define MAPBLOCKSHIFT 23
#define MAXRADIUS (32*FRACUNIT)
#define BOXTOP 0
#define BOXBOTTOM 1
#define BOXLEFT 2
#define BOXRIGHT 3
enum { ST_HORIZONTAL, ST_VERTICAL, ST_POSITIVE, ST_NEGATIVE };
#define ML_BLOCKING 1
#define ML_BLOCKMONSTERS 2
#define ML_TWOSIDED 4
#define MF_SPECIAL 1
#define MF_SOLID 2
#define MF_SHOOTABLE 4
#define MF_NOCLIP 0x1000
#define MF_PICKUP 0x800
#define MF_MISSILE 0x10000
#define MF_SKULLFLY 0x1000000
#define MF_NOSECTOR 8
#define MF_NOBLOCKMAP 16
#define MF_DROPOFF 0x400
#define MF_FLOAT 0x4000
#define MF_TELEPORT 0x8000
#define MAXSPECIALCROSS_ORIGINAL 8
#define MT_PLAYER 0
#define MT_KNIGHT 1
#define MT_BRUISER 2
#define LINKED_LIST_CHECK_NO_CYCLE(type,head,field) ((void)0)
typedef struct { fixed_t x,y; } vertex_t;
struct mobj_s;
typedef struct { fixed_t floorheight,ceilingheight; struct mobj_s *thinglist; int ceilingpic; int blockbox[4]; } sector_t;
typedef struct { sector_t *sector; } subsector_t;
typedef struct { int damage,spawnstate; } info_t;
typedef struct player_s player_t;
typedef struct { int ordinal; } state_t;
static state_t states[5];
typedef struct mobj_s {
    fixed_t x,y,z,radius,height,momx,momy,momz,floorz,ceilingz;
    int flags,type;
    player_t *player;
    state_t *state;
    unsigned int angle;
    int health,sprite,removed;
    struct mobj_s *target,*bnext,*bprev,*snext,*sprev;
    subsector_t *subsector;
    info_t *info;
} mobj_t;
typedef struct {
    vertex_t *v1,*v2;
    fixed_t dx,dy,bbox[4];
    int slopetype,flags,special,validcount;
    short sidenum[2];
    sector_t *frontsector,*backsector;
} line_t;
static line_t lines[64],*ceilingline,*spechit[64];
static vertex_t vertices[128];
static sector_t sectors[128],base_sector;
static subsector_t base_subsector={&base_sector};
static sector_t world_sectors[2];
static subsector_t world_subsectors[2]={{&world_sectors[0]},{&world_sectors[1]}};
static int use_world,floatok,effect_mode;
static fixed_t world_split,effect_x,effect_y;
static int cross_events[64][5],cross_count,checked_count,checked_clear;
static mobj_t things[64],mover,*blocklinks[64],*tmthing;
static short blockmaplump[4096],*blockmap=blockmaplump+4;
static int bmapwidth=1,bmapheight=1;
static fixed_t bmaporgx,bmaporgy,tmx,tmy,tmbbox[4],tmfloorz,tmceilingz,tmdropoffz;
static fixed_t opentop,openbottom,openrange,lowfloor;
static int tmflags,validcount,numspechit,deh_species_infighting;
static int line_count,thing_count,lump_size,visited_lines[64],nlines,visited_things[256],nthings;
static subsector_t *R_PointInSubsector(fixed_t x,fixed_t y) {
    (void)y; return use_world ? &world_subsectors[x<world_split?0:1] : &base_subsector;
}
static void P_CrossSpecialLine(int line,int side,mobj_t *thing);
static void SpechitOverrun(line_t *line) { (void)line; abort(); }
static int missile_fixture,missile_roll,missile_target,missile_damage;
static int P_Random(void) { assert(missile_fixture);return missile_roll; }
static void P_DamageMobj(mobj_t *a,mobj_t *b,mobj_t *c,int d) { (void)b;(void)c;assert(missile_fixture);missile_target=(int)(a-things);missile_damage=d; }
static void P_SetMobjState(mobj_t *a,int b) { assert(a->player && b>=0 && b<5);a->state=&states[b]; }
static void P_TouchSpecialThing(mobj_t *a,mobj_t *b);

static void print_scene(void);

/* REFERENCE_FUNCTIONS */

static void reset_scene(void) {
    memset(lines,0,sizeof(lines)); memset(things,0,sizeof(things));
    memset(blocklinks,0,sizeof(blocklinks)); memset(blockmaplump,0,sizeof(blockmaplump));
    line_count=thing_count=validcount=0;
    use_world=effect_mode=world_split=effect_x=effect_y=0;
    memset(world_sectors,0,sizeof(world_sectors));
    world_sectors[0].ceilingheight=world_sectors[1].ceilingheight=128*FRACUNIT;
    bmaporgx=bmaporgy=0; bmapwidth=bmapheight=1;
    blockmap[0]=5; blockmaplump[5]=0; blockmaplump[6]=-1; lump_size=7;
}
static void print_ids(int *ids,int n) { printf("%d",n); for(int i=0;i<n;i++) printf(" %d",ids[i]); }
static void print_result_fields(int clear) {
    printf("%d %d %d %d %td %d",clear,tmfloorz,tmceilingz,tmdropoffz,
        ceilingline ? ceilingline-lines : -1,numspechit);
    for(int i=0;i<numspechit;i++) printf(" %td",spechit[i]-lines);
    printf(" | "); print_ids(visited_things,nthings);
    printf(" | "); print_ids(visited_lines,nlines);
}
static void print_result(int clear) { print_result_fields(clear); putchar('\n'); }
static int sector_id(mobj_t *thing) {
    return thing->subsector==&world_subsectors[1] ? 1 : 0;
}
static void print_chain(mobj_t *head,int sector) {
    int ids[64],n=0; mobj_t *prev=NULL;
    for(mobj_t *t=head;t;t=sector?t->snext:t->bnext) {
        assert(n<64 && (sector?t->sprev:t->bprev)==prev);
        ids[n++]=(int)(t-things);prev=t;
    }
    printf(" / ");print_ids(ids,n);
}
static void print_scene(void) {
    printf("%d",thing_count);
    for(int i=0;i<thing_count;i++) {
        mobj_t *t=&things[i];printf(" %d %d %d %d %d %d %d",t->x,t->y,t->z,t->height,t->floorz,t->ceilingz,sector_id(t));
    }
    printf(" | 2");for(int i=0;i<2;i++) print_chain(world_sectors[i].thinglist,1);
    printf(" | %d",bmapwidth*bmapheight);
    for(int i=0;i<bmapwidth*bmapheight;i++) print_chain(blocklinks[i],0);
}
static void P_CrossSpecialLine(int line,int side,mobj_t *thing) {
    assert(cross_count<64);
    if(!(thing->flags&MF_NOSECTOR)) assert(thing->subsector->sector->thinglist==thing);
    int *event=cross_events[cross_count++];
    event[0]=line;event[1]=side;event[2]=thing->x;event[3]=thing->y;event[4]=sector_id(thing);
    if(effect_mode==1) { for(int i=0;i<line_count;i++) lines[i].special=0; }
    if(effect_mode==2) {
        P_UnsetThingPosition(thing);thing->x=effect_x;thing->y=effect_y;P_SetThingPosition(thing);
    }
}
int main(int argc,char **argv) {
    if(argc!=2) return 2;
    FILE *in=fopen(argv[1],"r"); if(!in) return 2;
    char text[1024]; reset_scene();
    while(fgets(text,sizeof(text),in)) {
        char *op=strtok(text," \n"); if(!op) continue;
        int32_t a[64]; int n=0; char *p;
        while((p=strtok(NULL," \n"))) { assert(n<64); a[n++]=(int32_t)strtoll(p,NULL,10); }
        if(hitscan_command(op,a,n) || use_command(op,a,n) || sector_command(op,a,n)) {}
        else if(!strcmp(op,"height") && n==7) {
            mobj_t t={.z=a[0],.height=a[1],.floorz=a[2],.ceilingz=a[3]};
            clip_supplied=1;clip_floor=a[4];clip_ceiling=a[5];clip_clear=a[6];clip_checks=0;
            int fits=P_ThingHeightClip(&t);
            printf("%d %d %d %d %d %d\n",fits,t.z,t.floorz,t.ceilingz,clip_checks,clip_result);clip_supplied=0;
        } else if(!strcmp(op,"clip") && n==2) {
            assert(use_world && a[0]>=0 && a[0]<thing_count && (a[1]==0||a[1]==1));
            mobj_t *t=&things[a[0]];player_t *old=t->player;
            if(!a[1])t->player=NULL;
            nlines=nthings=clip_checks=0;clip_supplied=0;
            int fits=P_ThingHeightClip(t);t->player=old;
            printf("%d | ",fits);print_result_fields(clip_result);printf(" | ");print_scene();putchar('\n');
        } else if(!strcmp(op,"reset") && n==0) { reset_scene(); puts("reset"); }
        else if(!strcmp(op,"grid") && n==4) {
            assert(a[2]>0&&a[2]<=8&&a[3]>0&&a[3]<=8);
            bmaporgx=(int32_t)((uint32_t)a[0]*65536u); bmaporgy=(int32_t)((uint32_t)a[1]*65536u);
            bmapwidth=a[2];bmapheight=a[3];lump_size=4+bmapwidth*bmapheight;
            memset(blocklinks,0,sizeof(blocklinks));
            for(int i=0;i<bmapwidth*bmapheight;i++) {
                blockmap[i]=lump_size;blockmaplump[lump_size++]=0;blockmaplump[lump_size++]=-1;
            } puts("grid");
        } else if(!strcmp(op,"line") && n==9) {
            int i=line_count++; assert(i<64); line_t *l=&lines[i];
            l->v1=&vertices[2*i];l->v2=&vertices[2*i+1];
            l->v1->x=a[0];l->v1->y=a[1];l->v2->x=a[2];l->v2->y=a[3];
            l->dx=a[2]-a[0];l->dy=a[3]-a[1];
            l->bbox[BOXLEFT]=a[0]<a[2]?a[0]:a[2]; l->bbox[BOXRIGHT]=a[0]>a[2]?a[0]:a[2];
            l->bbox[BOXBOTTOM]=a[1]<a[3]?a[1]:a[3];l->bbox[BOXTOP]=a[1]>a[3]?a[1]:a[3];
            if(!l->dx) l->slopetype=ST_VERTICAL;
            else if(!l->dy) l->slopetype=ST_HORIZONTAL;
            else { assert(l->dx!=INT_MIN && l->dy!=INT_MIN);l->slopetype=FixedDiv(l->dy,l->dx)>0?ST_POSITIVE:ST_NEGATIVE; }
            l->frontsector=&sectors[2*i]; *l->frontsector=(sector_t){.floorheight=a[4],.ceilingheight=a[5]};
            l->backsector=(a[8]&1)?&sectors[2*i+1]:NULL; l->sidenum[1]=l->backsector?1:-1;
            if(l->backsector) *l->backsector=(sector_t){.floorheight=a[6],.ceilingheight=a[7]};
            l->flags=((a[8]&2)?ML_BLOCKING:0)|((a[8]&8)?ML_BLOCKMONSTERS:0);l->special=!!(a[8]&4);
            if(l->backsector && !(a[8]&16)) l->flags |= ML_TWOSIDED;
            printf("line %d\n",i);
        } else if(!strcmp(op,"cell") && n>=1) {
            assert(a[0]>=0&&a[0]<bmapwidth*bmapheight&&lump_size+n+1<4096);
            blockmap[a[0]]=lump_size; blockmaplump[lump_size++]=0;
            for(int i=1;i<n;i++) { assert(a[i]>=0&&a[i]<line_count);blockmaplump[lump_size++]=a[i]; }
            blockmaplump[lump_size++]=-1; puts("cell");
        } else if(!strcmp(op,"thing") && n==4) {
            int i=thing_count++; assert(i<64);
            things[i]=(mobj_t){.x=a[0],.y=a[1],.radius=a[2],.flags=a[3]?MF_SOLID:0,
                .height=56*FRACUNIT,.ceilingz=128*FRACUNIT};
            printf("thing %d\n",i);
        } else if(!strcmp(op,"link") && n>=1) {
            assert(a[0]>=0&&a[0]<bmapwidth*bmapheight);mobj_t **tail=&blocklinks[a[0]];
            for(int i=1;i<n;i++) {assert(a[i]>=0&&a[i]<thing_count);*tail=&things[a[i]];tail=&things[a[i]].bnext;}
            *tail=NULL;puts("link");
        } else if(!strcmp(op,"query") && n==7) {
            base_sector=(sector_t){.floorheight=a[3],.ceilingheight=a[4]};nlines=nthings=0;
            mover=(mobj_t){.radius=a[2],.flags=MF_SOLID|(a[6]?MF_NOCLIP:0),.player=(player_t*)&mover};
            mobj_t *m=&mover; int oldflags=0;void *oldplayer=NULL;
            if(a[5]>=0) { assert(a[5]<thing_count);m=&things[a[5]];assert(m->radius==a[2] && m->flags==MF_SOLID);
                oldflags=m->flags;oldplayer=m->player;m->flags=mover.flags;m->player=(player_t*)&mover; }
            int clear=P_CheckPosition(m,a[0],a[1]);print_result(clear);
            if(a[5]>=0) {m->flags=oldflags;m->player=oldplayer;}
        } else if(!strcmp(op,"world") && n==5) {
            use_world=1;world_sectors[0].floorheight=a[0];world_sectors[0].ceilingheight=a[1];
            world_sectors[1].floorheight=a[2];world_sectors[1].ceilingheight=a[3];world_split=a[4];puts("world");
        } else if(!strcmp(op,"body") && n==6) {
            assert(a[0]>=0&&a[0]<thing_count);mobj_t *t=&things[a[0]];
            t->z=a[1];t->height=a[2];t->floorz=a[3];t->ceilingz=a[4];t->player=(player_t*)t;
            t->flags=(t->flags&MF_SOLID)|((a[5]&1)?MF_NOCLIP:0)|((a[5]&2)?MF_TELEPORT:0)|
                ((a[5]&4)?MF_DROPOFF:0)|((a[5]&8)?MF_FLOAT:0)|((a[5]&16)?MF_NOSECTOR:0)|((a[5]&32)?MF_NOBLOCKMAP:0);
            puts("body");
        } else if(!strcmp(op,"place") && n==1) {
            assert(use_world&&a[0]>=0&&a[0]<thing_count);P_SetThingPosition(&things[a[0]]);
            printf("placed | ");print_scene();putchar('\n');
        } else if(!strcmp(op,"effect") && n==3) {
            assert(a[0]>=0&&a[0]<=2);effect_mode=a[0];effect_x=a[1];effect_y=a[2];puts("effect");
        } else if(!strcmp(op,"try") && n==3) {
            assert(use_world&&a[0]>=0&&a[0]<thing_count);nlines=nthings=cross_count=0;
            int accepted=P_TryMove(&things[a[0]],a[1],a[2]);
            printf("%d %d | ",accepted,floatok);
            int remaining=numspechit;numspechit=checked_count;print_result_fields(checked_clear);numspechit=remaining;
            printf(" | ");print_scene();printf(" | %d",cross_count);
            for(int i=0;i<cross_count;i++) for(int j=0;j<5;j++) printf(" %d",cross_events[i][j]);
            putchar('\n');
        } else if(!strcmp(op,"point") && n==3) {
            assert(a[0]>=0&&a[0]<line_count); printf("%d\n",P_PointOnLineSide(a[1],a[2],&lines[a[0]]));
        } else if(!strcmp(op,"box") && n==5) {
            assert(a[0]>=0&&a[0]<line_count);printf("%d\n",P_BoxOnLineSide(a+1,&lines[a[0]]));
        } else if(!strcmp(op,"coord") && n==2) printf("%d\n",(a[0]-a[1])>>MAPBLOCKSHIFT);
        else if(!strcmp(op,"missilething") && n==5) {
            mobj_t *t=&things[a[0]];t->type=a[1];t->z=a[2];t->height=a[3];t->flags=a[4];puts("missilething");
        } else if(!strcmp(op,"missilequery") && n==6) {
            info_t info={.damage=3};mobj_t source={.type=a[4]};
            mover=(mobj_t){.radius=6*FRACUNIT,.height=8*FRACUNIT,.z=a[2],.flags=MF_MISSILE|MF_DROPOFF,.info=&info,.target=a[3]<0?NULL:&source};
            if(a[3]>=0 && a[3]<thing_count)mover.target=&things[a[3]];
            base_sector=(sector_t){.floorheight=0,.ceilingheight=128*FRACUNIT};nlines=nthings=0;
            missile_fixture=1;missile_roll=a[5];missile_target=-1;missile_damage=0;
            int clear=P_CheckPosition(&mover,a[0],a[1]);print_result_fields(clear);printf(" | %d %d\n",missile_target,missile_damage);missile_fixture=0;
        }
        else if(path_command(op,a,n) || world_command(op,a,n) || contact_command(op,a,n)) {}
        else return 3;
    }
    fclose(in);return 0;
}

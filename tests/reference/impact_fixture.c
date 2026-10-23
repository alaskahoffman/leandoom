/* Bounded host for unchanged original spawn/Z movement/state routines.
 * No XY motion, collision, map traversal, allocation policy or sound oracle. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int fixed_t,boolean,statenum_t,mobjtype_t;
typedef struct mobj_s mobj_t;
typedef void (*actionf_v)(void);
typedef void (*actionf_p1)(void *);
typedef union {actionf_v acv;actionf_p1 acp1;} action_t;
typedef struct {action_t function;} thinker_t;
typedef struct {int sprite,frame,tics;action_t action;int nextstate;} state_t;
typedef struct {int spawnstate,spawnhealth,reactiontime,radius,height,flags;} mobjinfo_t;
typedef struct {int floorheight,ceilingheight;} sector_t;
typedef struct {sector_t *sector;} subsector_t;
typedef struct {int viewheight,deltaviewheight;} player_t;
struct mobj_s {
 thinker_t thinker; int type,x,y,z,momx,momy,momz,radius,height,flags,health;
 int reactiontime,lastlook,tics,sprite,frame,floorz,ceilingz,movecount,removed;
 mobjinfo_t *info; state_t *state; subsector_t *subsector; player_t *player;
 mobj_t *target;
};
#define FRACUNIT 65536
#define GRAVITY FRACUNIT
#define VIEWHEIGHT (41*FRACUNIT)
#define FLOATSPEED (4*FRACUNIT)
#define MELEERANGE (64*FRACUNIT)
#define ONFLOORZ INT_MIN
#define ONCEILINGZ INT_MAX
#define MAXPLAYERS 4
#define PU_LEVEL 50
#define TICRATE 35
#define MF_NOBLOCKMAP 16
#define MF_NOGRAVITY 512
#define MF_FLOAT 0x4000
#define MF_SKULLFLY 0x1000000
#define MF_INFLOAT 0x200000
#define MF_MISSILE 0x10000
#define MF_NOCLIP 0x1000
#define MF_COUNTKILL 0x400000
#define MOBJ_CYCLE_LIMIT 1000000
#define S_NULL 0
enum {MT_PUFF,MT_BLOOD,sk_nightmare=4,exe_ultimate=10,sfx_oof=1};
static int gameskill=2,gameversion=9,respawnmonsters=0,leveltime,attackrange;
static sector_t sector; static subsector_t sub={&sector}; static mobj_t object;
static void P_MobjThinker(mobj_t *);
static void I_Error(const char *s){fprintf(stderr,"%s\n",s);abort();}
static void *Z_Malloc(size_t n,int tag,void *owner){assert(n==sizeof(object));(void)tag;(void)owner;return &object;}
static void P_SetThingPosition(mobj_t *m){m->subsector=&sub;}
static void P_AddThinker(thinker_t *t){(void)t;}
static void P_RemoveMobj(mobj_t *m){m->removed=1;m->thinker.function.acv=(actionf_v)(-1);}
static int P_AproxDistance(int x,int y){(void)x;(void)y;abort();}
static void P_ExplodeMissile(mobj_t *m){(void)m;abort();}
static void P_NightmareRespawn(mobj_t *m){(void)m;abort();}
static void P_XYMovement(mobj_t *m){(void)m;abort();}
static void S_StartSound(mobj_t *m,int s){(void)m;(void)s;abort();}
/* TABLES */
/* ROUTINES */
static void dump(void){printf("%d %d %d %d %td %d %d %d %d\n",object.x,object.y,object.z,object.momz,
 object.state?object.state-states:0,object.tics,object.lastlook,prndindex,object.removed);}
int main(int argc,char **argv){
 assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);
 int blood,damage,melee,rng,x,y,z,floor,ceiling,steps;
 while(fscanf(f,"%d%d%d%d%d%d%d%d%d%d",&blood,&damage,&melee,&rng,&x,&y,&z,&floor,&ceiling,&steps)==10){
  sector=(sector_t){floor,ceiling};prndindex=rng;attackrange=melee?MELEERANGE:2048*FRACUNIT;
  if(blood)P_SpawnBlood(x,y,z,damage);else P_SpawnPuff(x,y,z);
  dump();for(int i=0;i<steps;i++){if(!object.removed)P_MobjThinker(&object);dump();}
 }
 fclose(f);return 0;
}

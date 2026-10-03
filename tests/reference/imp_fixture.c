#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
typedef int fixed_t;typedef unsigned angle_t;typedef int boolean;typedef int dirtype_t;
#define FRACBITS 16
#define S_NULL 0
#define FRACUNIT 65536
#define FINEANGLES 8192
#define SLOPERANGE 2048
#define ANG90 0x40000000
#define ANG180 0x80000000
#define ANG270 0xc0000000
#define MF_SHOOTABLE 4
#define MF_AMBUSH 32
#define MF_JUSTHIT 64
#define MF_JUSTATTACKED 128
#define MF_SHADOW 0x40000
#define MF_FLOAT 0x4000
#define MF_INFLOAT 0x200000
#define MELEERANGE (64*FRACUNIT)
#define FLOATSPEED (4*FRACUNIT)
#define MT_VILE 64
#define MT_UNDEAD 66
#define MT_CYBORG 16
#define MT_SPIDER 7
#define MT_SKULL 3006
#define MT_TROOPSHOT 999
#define exe_doom_1_2 2
#define exe_doom_1_5 5
#define sk_nightmare 4
enum {DI_EAST,DI_NORTHEAST,DI_NORTH,DI_NORTHWEST,DI_WEST,DI_SOUTHWEST,DI_SOUTH,DI_SOUTHEAST,DI_NODIR};
enum {sfx_None,sfx_posit1,sfx_posit2,sfx_posit3,sfx_bgsit1,sfx_bgsit2,sfx_bgact,sfx_popain,sfx_claw,sfx_firsht,sfx_firxpl};
static const char *sounds[]={"None","posit1","posit2","posit3","bgsit1","bgsit2","bgact","popain","claw","firsht","firxpl"};
typedef struct mobj_s mobj_t;
typedef struct {int spawnstate,seestate,meleestate,missilestate,seesound,attacksound,activesound,speed,radius,painsound,deathstate,deathsound;} info_t;
typedef struct {int health;mobj_t *mo;} player_t;
typedef struct {mobj_t *soundtarget;} sector_t;
typedef struct {sector_t *sector;} subsector_t;
typedef struct {void(*acp1)(mobj_t *);} action_t;
typedef struct {int sprite,frame,tics;action_t action;int nextstate,misc1,misc2;} state_t;
typedef struct {int dummy;} line_t;
struct mobj_s {int x,y,z,floorz,momx,momy,momz,height,radius,removed,health,type,flags,movedir,movecount,reactiontime,threshold,lastlook,tics;unsigned angle;mobj_t *target;info_t *info;subsector_t *subsector;state_t *state;};
static mobj_t actor,target;
static sector_t sector;static subsector_t sub={&sector};
static player_t players[4];static int playeringame[4]={1,0,0,0};
static int gameversion=9,gameskill=2,fastparm,netgame,numspechit,floatok;
static fixed_t tmfloorz,viewx,viewy;static line_t *spechit[8];
static int mask,cansee,moves[100],move_count;
static char trace[1024];
static void event(const char *fmt,...){va_list args;va_start(args,fmt);vsnprintf(trace+strlen(trace),sizeof(trace)-strlen(trace),fmt,args);va_end(args);}
static void I_Error(const char *s){(void)s;abort();}
static boolean P_CheckSight(mobj_t *a,mobj_t *b){(void)a;(void)b;return cansee;}
static boolean P_TryMove(mobj_t *a,int x,int y){if(a->type==MT_TROOPSHOT)return mask!=0;moves[move_count++]=a->movedir;if(!(mask&(1<<a->movedir)))return 0;a->x=x;a->y=y;return 1;}
static boolean P_UseSpecialLine(mobj_t *a,line_t *l,int side){(void)a;(void)l;(void)side;abort();}
static void S_StartSound(mobj_t *a,int sound){(void)a;event(" sound %s",sounds[sound]);}
static void P_DamageMobj(mobj_t *a,mobj_t *b,mobj_t *c,int n){(void)a;(void)b;(void)c;event(" damage %d",n);}
static void P_SpawnMissile(mobj_t *a,mobj_t *b,int type){(void)a;(void)b;assert(type==MT_TROOPSHOT);event(" missile");}
static void A_Look(mobj_t *);static void A_Chase(mobj_t *);static void A_FaceTarget(mobj_t *);static void A_TroopAttack(mobj_t *);
static void A_Pain(mobj_t *a){S_StartSound(a,a->info->painsound);}
/* TABLES */
static void P_SetMobjState(mobj_t *a,int id){if(!id){a->removed=1;return;}a->state=&states[id];a->tics=a->state->tics;if(a->state->action.acp1)a->state->action.acp1(a);}
/* ROUTINES */
/* PROJECTILES */
static int next(void){char *s=strtok(NULL," \r\n");assert(s);return (int)strtol(s,NULL,10);}
static void dump(int answer){
 printf("%d %td %d %u %d %d %d %d %d %d %d %d %d %d %d %d /%s /",answer,actor.state-states,actor.tics,actor.angle,actor.target!=NULL,actor.movedir,actor.movecount,actor.reactiontime,actor.threshold,actor.lastlook,!!(actor.flags&MF_AMBUSH),!!(actor.flags&MF_JUSTHIT),!!(actor.flags&MF_JUSTATTACKED),prndindex,actor.x,actor.y,trace);
 for(int i=0;i<move_count;i++)printf(" %d",moves[i]);puts("");
}
int main(int argc,char **argv){assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char buf[1024];
 while(fgets(buf,sizeof(buf),f)){
  char *op=strtok(buf," \r\n");if(!op)continue;trace[0]=0;move_count=0;int answer=-1;
  if(!strcmp(op,"spawn")){
   actor=(mobj_t){.type=3001};target=(mobj_t){0};actor.x=next();actor.y=next();actor.z=next();target.x=next();target.y=next();target.z=next();
   if(next())target.flags|=MF_SHADOW;prndindex=next();mask=next();
   mobj_t *p=Original_SpawnMissile(&actor,&target,MT_TROOPSHOT);
   printf("%d %d %d %d %d %d %u %td %d %d %d\n",p->x,p->y,p->z,p->momx,p->momy,p->momz,p->angle,p->state-states,p->tics,!(p->flags&MF_MISSILE),prndindex);continue;
  }
  if(!strcmp(op,"setup")){
   actor=(mobj_t){.info=&impinfo,.subsector=&sub,.health=60,.type=3001,.state=&states[S_TROO_STND],.tics=10};
   target=(mobj_t){.info=&playerinfo,.subsector=&sub,.flags=MF_SHOOTABLE};
   actor.x=next();actor.y=next();target.x=next();target.y=next();actor.angle=next();actor.target=next()?&target:NULL;actor.movedir=next();mask=next();cansee=next();sector.soundtarget=next()?&target:NULL;
   if(next())actor.flags|=MF_AMBUSH;if(next())target.flags|=MF_SHADOW;
   actor.reactiontime=next();actor.movecount=next();actor.threshold=next();if(next())actor.flags|=MF_JUSTHIT;if(next())actor.flags|=MF_JUSTATTACKED;
   actor.lastlook=next();prndindex=next();target.health=next();if(target.health<=0)target.flags&=~MF_SHOOTABLE;players[0]=(player_t){target.health,&target};
  }else if(!strcmp(op,"enter"))P_SetMobjState(&actor,next());
  else if(!strcmp(op,"tick")){if(!--actor.tics)P_SetMobjState(&actor,actor.state->nextstate);}
  else if(!strcmp(op,"newdir"))P_NewChaseDir(&actor);
  else if(!strcmp(op,"melee"))answer=P_CheckMeleeRange(&actor);
  else if(!strcmp(op,"range"))answer=P_CheckMissileRange(&actor);
  else abort();dump(answer);
 }fclose(f);return 0;
}

/* Unchanged P_DamageMobj in a player-only host; kill/retarget are explicit
 * boundaries. Original state metadata and countdown drive the second output.
 * GPL-2.0-or-later. */
#include <assert.h>
#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int fixed_t; typedef unsigned angle_t; typedef int boolean;
#define FRACBITS 16
#define FRACUNIT 65536
#define FINEANGLES 8192
#define SLOPERANGE 2048
#define ANG90 0x40000000
#define ANG180 0x80000000
#define ANG270 0xc0000000
#define ANGLETOFINESHIFT 19
#define MF_SHOOTABLE 4
#define MF_SKULLFLY 0x1000000
#define MF_NOCLIP 0x1000
#define MF_JUSTHIT 64
#define CF_GODMODE 2
#define wp_chainsaw 7
#define sk_baby 0
#define pw_invulnerability 0
#define MT_VILE 3
#define BASETHRESHOLD 100
#define S_NULL 0
#define exe_doom_1_5 5
typedef struct mobj_s mobj_t;
typedef struct {int health,cheats,powers[1],armortype,armorpoints,damagecount,readyweapon;mobj_t *attacker;} player_t;
typedef struct {int special;} sector_t;
typedef struct {sector_t *sector;} subsector_t;
typedef struct {int tics,nextstate,pain;} state_t;
typedef struct {int mass,painchance,painstate,spawnstate,seestate;} info_t;
struct mobj_s {int flags,health,x,y,z,momx,momy,momz,reactiontime,threshold,type,tics;
 player_t *player;subsector_t *subsector;info_t *info;state_t *state;mobj_t *target;};
static player_t players[1]; static int consoleplayer,gameskill,gameversion=9;
static int killed,pain,applied; static fixed_t viewx,viewy;
/* TABLES */
static void I_Tactile(int a,int b,int c){(void)a;(void)b;(void)c;applied=1;}
static void P_KillMobj(mobj_t *source,mobj_t *target){(void)source;(void)target;killed=1;}
static boolean P_SetMobjState(mobj_t *m,int s){m->state=&states[s];m->tics=states[s].tics;pain=1;return 1;}
/* ROUTINES */
static int next(void){char *s=strtok(NULL," \r\n");assert(s);return (int)strtol(s,NULL,10);}
int main(int argc,char **argv){
 assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char buf[1024];
 while(fgets(buf,sizeof(buf),f)){
  int v[27];char *p=strtok(buf," \r\n");if(!p)continue;v[0]=(int)strtol(p,NULL,10);
  for(int i=1;i<27;i++)v[i]=next();killed=pain=applied=0;prndindex=v[24];
  sector_t sector={v[16]};subsector_t sub={&sector};info_t info={100,255,156,149,0};
  players[0]=(player_t){.health=v[7],.armorpoints=v[8],.armortype=v[9],.damagecount=v[10],.cheats=v[14]?CF_GODMODE:0,.powers={v[15]}};
  player_t attacker={.readyweapon=v[22]?wp_chainsaw:1};
  mobj_t source={.player=&attacker},inflictor={.x=v[18],.y=v[19],.z=v[20]};
  mobj_t m={.x=v[0],.y=v[1],.z=v[2],.momx=v[3],.momy=v[4],.momz=v[5],.health=v[6],
   .flags=(v[11]?MF_SHOOTABLE:0)|(v[12]?MF_SKULLFLY:0)|(v[13]?MF_NOCLIP:0),
   .player=&players[0],.subsector=&sub,.info=&info,.state=&states[149]};
  gameskill=v[23]?sk_baby:2;
  P_DamageMobj(&m,v[17]?&inflictor:NULL,&source,v[21]);
  printf("%d %d %d %d %d %d %d %d %d %d %d %d\n",m.momx,m.momy,m.momz,m.health,players[0].health,
   players[0].armorpoints,players[0].armortype,players[0].damagecount,prndindex,applied,killed,pain);
  m.state=&states[v[25]];m.tics=v[26];
  for(int i=0;i<16;i++){
   int sound=0;
   if(m.tics!=-1){m.tics--;if(!m.tics){m.state=&states[m.state->nextstate];m.tics=m.state->tics;sound=m.state->pain;}}
   printf(" %td:%d:%d",m.state-states,m.tics,sound);
  }puts("");
 }fclose(f);return 0;
}

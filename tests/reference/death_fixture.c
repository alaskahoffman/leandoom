#include <assert.h>
#include <stdbool.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int boolean;typedef int statenum_t;typedef int mobjtype_t;
#define MF_SHOOTABLE 4
#define MF_SOLID 2
#define MF_FLOAT 0x4000
#define MF_SKULLFLY 0x1000000
#define MF_NOGRAVITY 0x200
#define MF_CORPSE 0x100000
#define MF_DROPOFF 0x400
#define MF_COUNTKILL 0x400000
#define MF_PICKUP 0x800
#define MF_NOTDMATCH 0x2000000
#define MF_NOBLOOD 0x80000
#define MF_DROPPED 0x20000
#define ONFLOORZ (-2147483647-1)
#define MOBJ_CYCLE_LIMIT 1000000
#define MT_PLAYER 0
#define MT_POSSESSED 3004
#define MT_SHOTGUY 9
#define MT_CHAINGUY 65
#define MT_WOLFSS 84
#define MT_SKULL 3006
#define MT_SPIDER 7
#define MT_CYBORG 16
#define MT_CLIP 2007
#define MT_SHOTGUN 2001
#define MT_CHAINGUN 2002
#define commercial 1
#define exe_chex 1
#define PST_DEAD 1
enum {sfx_None=0,sfx_podth1,sfx_podth2,sfx_podth3,sfx_bgdth1,sfx_bgdth2,sfx_sgtdth,sfx_slop,sfx_pldeth,sfx_pdiehi,sfx_barexp};
static const char *sounds[]={"None","podth1","podth2","podth3","bgdth1","bgdth2","sgtdth","slop","pldeth","pdiehi","barexp"};
typedef struct {int killcount,frags[4],playerstate;} player_t;
typedef struct mobj_s mobj_t;
typedef struct {void (*acp1)(mobj_t *);} action_t;
typedef struct {int sprite,frame,tics;action_t action;int nextstate,misc1,misc2;} state_t;
typedef struct {int spawnhealth,deathstate,xdeathstate,deathsound,flags;} info_t;
struct mobj_s {int flags,type,height,health,tics,sprite,frame,x,y,removed;mobj_t *target;player_t *player;info_t *info;state_t *state;};
static player_t players[4];
static int netgame,consoleplayer,automapactive,gameversion,gamemode;
static char trace[4096];
static void event(const char *format,...){va_list args;va_start(args,format);size_t n=strlen(trace);vsnprintf(trace+n,sizeof(trace)-n,format,args);va_end(args);}
static void I_Error(const char *fmt,...){(void)fmt;abort();}
static void P_RemoveMobj(mobj_t *m){m->removed=1;event(" remove");}
static void P_DropWeapon(player_t *p){event(" weapon %td",p-players);}
static void AM_Stop(void){automapactive=0;event(" automap");}
static void S_StartSound(mobj_t *m,int sound){event(" sound %s %d",sounds[sound],m==NULL);}
static mobj_t dropped;
static mobj_t *P_SpawnMobj(int x,int y,int z,int item){(void)x;(void)y;assert(z==ONFLOORZ);event(" drop %d",item);dropped=(mobj_t){0};return &dropped;}
static void P_RadiusAttack(mobj_t *spot,mobj_t *source,int damage){(void)spot;(void)source;assert(damage==128);event(" explode");}
static void A_Explode(mobj_t *);
static void A_Scream(mobj_t *);
static void A_XScream(mobj_t *);
static void A_Fall(mobj_t *);
static void A_PlayerScream(mobj_t *);
/* TABLES */
/* RNG */
/* ROUTINES */
static int next(void){char *s=strtok(NULL," \r\n");assert(s);return (int)strtol(s,NULL,10);}
static void dump(mobj_t *m){
    printf("%u %d %d %td %d %d %d %d",(unsigned)m->flags,m->height,m->health,m->state?m->state-states:0,m->tics,m->removed,automapactive,prndindex);
    for(int i=0;i<4;i++){printf(" | %d %d",players[i].killcount,players[i].playerstate);for(int j=0;j<4;j++)printf(" %d",players[i].frags[j]);}
    printf(" /%s\n",trace);
}
int main(int argc,char **argv){
    assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char buf[1024];mobj_t body={0},source={0};
    while(fgets(buf,sizeof(buf),f)){
        char *op=strtok(buf," \r\n");if(!op)continue;trace[0]=0;
        if(!strcmp(op,"kill")){
            int meta=next();body=(mobj_t){0};body.info=&infos[meta];body.type=next();body.flags=next();body.health=next();body.height=next();
            int victim=next(),src=next();body.player=victim<0?NULL:&players[victim];source.player=src<0?NULL:&players[src];
            netgame=next();automapactive=next();gamemode=next();gameversion=next();prndindex=next();int kills=next(),frags=next();
            memset(players,0,sizeof(players));for(int i=0;i<4;i++){players[i].killcount=kills;for(int j=0;j<4;j++)players[i].frags[j]=frags;}
            P_KillMobj(src==-2?NULL:&source,&body);
            if(body.type==MT_POSSESSED||body.type==MT_SHOTGUY||body.type==MT_WOLFSS||body.type==MT_CHAINGUY)if(!gameversion)assert(dropped.flags&MF_DROPPED);
        }else if(!strcmp(op,"tick")){if(!body.removed)tick(&body);}else abort();
        dump(&body);
    }fclose(f);return 0;
}

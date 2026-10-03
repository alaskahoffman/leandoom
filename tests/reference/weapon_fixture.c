/* Independent p_pspr fixture: original routines, supplied sound/geometry hooks.
 * GPL-2.0-or-later, id Software / Simon Howard. Adapter 2026-10-03. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef int32_t fixed_t; typedef uint32_t angle_t; typedef int boolean;
typedef int statenum_t; typedef int ammotype_t;
#define true 1
#define false 0
#define FRACBITS 16
#define FRACUNIT 65536
#define FINEANGLES 8192
#define FINEMASK 8191
#define WEAPONTOP (32*FRACUNIT)
#define WEAPONBOTTOM (128*FRACUNIT)
#define LOWERSPEED (6*FRACUNIT)
#define RAISESPEED (6*FRACUNIT)
#define BT_ATTACK 1
#define NUMAMMO 4
#define NUMPSPRITES 2
#define MELEERANGE (64*FRACUNIT)
#define MISSILERANGE (2048*FRACUNIT)
enum {wp_fist,wp_pistol,wp_shotgun,wp_chaingun,wp_missile,wp_plasma,wp_bfg,wp_chainsaw,wp_supershotgun,wp_nochange};
enum {am_clip,am_shell,am_cell,am_misl,am_noammo};
enum {shareware,commercial,PST_DEAD=1,ps_weapon=0,ps_flash=1,pw_strength=1};
enum {sfx_pistol,sfx_shotgn,sfx_punch,sfx_sawup,sfx_sawidl};
/* ENUMS */
typedef struct player_s player_t; typedef struct pspdef_s pspdef_t;
typedef struct {int sprite,frame,tics; union {void (*acp2)(player_t*,pspdef_t*);} action; int nextstate,misc1,misc2;} state_t;
struct pspdef_s {state_t *state; int tics; fixed_t sx,sy;};
typedef struct {state_t *state;angle_t angle;fixed_t x,y;} mobj_t;
struct player_s {pspdef_t psprites[2];int readyweapon,pendingweapon,ammo[4],maxammo[4],weaponowned[9],health,playerstate,refire,attackdown,extralight,powers[6];fixed_t bob;struct{int buttons;}cmd;mobj_t *mo;};
typedef struct{int ammo,upstate,downstate,readystate,atkstate,flashstate;} weaponinfo_t;
static weaponinfo_t weaponinfo[9]={
 {am_noammo,S_PUNCHUP,S_PUNCHDOWN,S_PUNCH,S_PUNCH1,0},
 {am_clip,S_PISTOLUP,S_PISTOLDOWN,S_PISTOL,S_PISTOL1,S_PISTOLFLASH},
 {am_shell,S_SGUNUP,S_SGUNDOWN,S_SGUN,S_SGUN1,S_SGUNFLASH1}};
static int leveltime,gamemode=shareware,deh_bfg_cells_per_shot=40,prndindex,hitdraws;
static fixed_t bulletslope,viewx,viewy;
static mobj_t *linetarget;
static char events[8192];
static void emit(const char *s){if(*events)strcat(events,";");strcat(events,s);}
static int P_Random(void);static int P_SubRandom(void);
static void P_SetPsprite(player_t*,int,int);
static void P_FireWeapon(player_t*);
static void P_BringUpWeapon(player_t*);
static void A_WeaponReady(player_t*,pspdef_t*);static void A_Lower(player_t*,pspdef_t*);static void A_Raise(player_t*,pspdef_t*);static void A_ReFire(player_t*,pspdef_t*);
static void A_FirePistol(player_t*,pspdef_t*);static void A_FireShotgun(player_t*,pspdef_t*);static void A_Punch(player_t*,pspdef_t*);
static void A_Light0(player_t*,pspdef_t*);static void A_Light1(player_t*,pspdef_t*);static void A_Light2(player_t*,pspdef_t*);
/* STATES */
static void S_StartSound(mobj_t *mo,int s){(void)mo;emit(s==sfx_pistol?"sound:pistol":s==sfx_shotgn?"sound:shotgn":"sound:punch");}
static void P_SetMobjState(mobj_t *mo,int n){mo->state=&states[n];}
static void P_NoiseAlert(mobj_t *a,mobj_t *b){(void)a;(void)b;emit("noise");}
static fixed_t P_AimLineAttack(mobj_t *mo,angle_t a,fixed_t r){(void)mo;(void)a;(void)r;linetarget=NULL;return 0;}
static void P_LineAttack(mobj_t *mo,angle_t a,fixed_t r,fixed_t slope,int damage){
 (void)mo;(void)r;(void)slope;char b[80];snprintf(b,sizeof(b),"shot:%u:%d",a,damage);emit(b);
 for(int i=0;i<hitdraws;i++)P_Random();
}
static angle_t R_PointToAngle2(fixed_t x,fixed_t y,fixed_t tx,fixed_t ty){(void)x;(void)y;(void)tx;(void)ty;return 0;}
/* ROUTINES */
int main(int argc,char **argv){
 if(argc!=3)return 2;FILE *in=fopen(argv[1],"r"),*out=fopen(argv[2],"w");if(!in||!out)return 2;
 player_t p={0};mobj_t mo={0};char line[256];
 while(fgets(line,sizeof(line),in)){
  events[0]=0;
  if(!strncmp(line,"reset ",6)){
   int w,b,s,owned,seed;unsigned a;sscanf(line+6,"%d%d%d%d%d%u",&w,&b,&s,&owned,&seed,&a);
   p=(player_t){.readyweapon=w,.pendingweapon=9,.ammo={b,s,0,0},.weaponowned={1,1,owned,0,0,0,0,0,0},.health=100,.attackdown=1,.mo=&mo};
   mo=(mobj_t){.state=&states[S_PLAY],.angle=a};p.psprites[0]=(pspdef_t){.state=&states[weaponinfo[w].readystate],.tics=1,.sy=WEAPONTOP};prndindex=seed;leveltime=0;
  }else if(!strncmp(line,"tick ",5)){
   int attack,choice,bob;sscanf(line+5,"%d%d%d%d",&attack,&choice,&bob,&hitdraws);
   p.cmd.buttons=attack;p.bob=bob;
   if(choice<3&&p.weaponowned[choice]&&choice!=p.readyweapon)p.pendingweapon=choice;
   P_MovePsprites(&p);leveltime++;
  }else if(!strncmp(line,"die",3)){p.health=0;p.playerstate=PST_DEAD;P_DropWeapon(&p);}
  else return 3;
  pspdef_t *w=&p.psprites[0],*f=&p.psprites[1];
  fprintf(out,"%d %d %d %d %ld %d %d %d %ld %d %d %d %d %d %d %d|%s\n",p.readyweapon,p.pendingweapon,p.ammo[0],p.ammo[1],w->state?w->state-states:0,w->tics,w->sx,w->sy,f->state?f->state-states:0,f->tics,f->sx,f->sy,p.refire,p.attackdown,p.extralight,prndindex,events);
 }
 fclose(out);fclose(in);return 0;
}

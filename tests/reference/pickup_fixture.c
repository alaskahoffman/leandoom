/* DOOM 1.9, single-player, unmodified gameplay constants. No collision stubs
 * pretending to perform pickup timing: this tests the touch/effect stage alone. */
#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdbool.h>
typedef int boolean;
typedef int fixed_t;
typedef int ammotype_t;
typedef int weapontype_t;
typedef int card_t;
_Static_assert(sizeof(int)==4 && CHAR_BIT==8 && (-1>>1)==-1, "C profile");
#define FRACUNIT 65536
#define NUMAMMO 4
#define BONUSADD 6
#define MAXHEALTH 100
#define INVULNTICS (30*35)
#define INVISTICS (60*35)
#define INFRATICS (120*35)
#define IRONTICS (60*35)
#define MF_SHADOW 1
#define MF_DROPPED 2
#define MF_COUNTITEM 4
enum { am_clip,am_shell,am_cell,am_misl,am_noammo };
enum { wp_fist,wp_pistol,wp_shotgun,wp_chaingun,wp_missile,wp_plasma,wp_bfg,wp_chainsaw,wp_supershotgun };
enum { it_bluecard,it_yellowcard,it_redcard,it_blueskull,it_yellowskull,it_redskull };
enum { pw_invulnerability,pw_strength,pw_invisibility,pw_ironfeet,pw_allmap,pw_infrared };
enum { sk_baby,sk_easy,sk_medium,sk_hard,sk_nightmare };
enum { sfx_itemup=1,sfx_wpnup,sfx_getpow };
enum { exe_doom_1_2=1,commercial=1 };
/* SPRITES_AND_MESSAGES */
#define DEH_String(x) (x)
typedef struct player_s player_t;
typedef struct { int special; } sector_t;
typedef struct { sector_t *sector; } subsector_t;
typedef struct { int angleturn,forwardmove,sidemove,buttons; } ticcmd_t;
typedef struct { fixed_t z,height;int health,flags,sprite,reactiontime;player_t *player;subsector_t *subsector; } mobj_t;
struct player_s {
    mobj_t *mo;
    int health,armorpoints,armortype,ammo[4],maxammo[4],weaponowned[9],readyweapon,pendingweapon;
    int cards[6],powers[6],backpack,bonuscount,itemcount;
    const char *message;
    int damagecount,fixedcolormap,playerstate,cheats,usedown;
    ticcmd_t cmd;
};
static player_t players[1];
static mobj_t body,special;
static int gameskill=sk_medium,gamemode=commercial,gameversion=2,netgame,deathmatch,consoleplayer;
static int removed,sound_event;
/* METADATA */
/* PICKUP_CONSTANTS */
static void I_Error(const char *format,...) { (void)format;abort(); }
static void P_RemoveMobj(mobj_t *mo) { assert(mo==&special);removed=1; }
static void S_StartSound(mobj_t *mo,int sound) { assert(mo==NULL && sound_event==0);sound_event=sound; }
/* PICKUP_FUNCTIONS */
/* PlayerThink dependencies are deliberately inert: only its original counter
 * stage and early dead-player return are under test, not action/death behavior. */
enum { PST_DEAD=1,CF_NOCLIP=1,MF_NOCLIP=8,MF_JUSTATTACKED=16,
       BT_SPECIAL=128,BT_CHANGE=4,BT_WEAPONMASK=56,BT_WEAPONSHIFT=3,BT_USE=2,shareware=2 };
static int counter_trace;
static void P_MovePlayer(player_t *p) { (void)p;counter_trace=counter_trace*10+1; }
static void P_CalcHeight(player_t *p) { (void)p;counter_trace=counter_trace*10+2; }
static void P_MovePsprites(player_t *p) { (void)p;counter_trace=counter_trace*10+3; }
static void P_DeathThink(player_t *p) { (void)p;counter_trace=counter_trace*10+4; }
static void P_PlayerInSpecialSector(player_t *p) { (void)p;abort(); }
static void P_UseLines(player_t *p) { (void)p;abort(); }
/* PLAYER_THINK */
static void reset(void) {
    memset(players,0,sizeof(players));memset(&body,0,sizeof(body));memset(&special,0,sizeof(special));
    player_t *p=players;p->mo=&body;body.player=p;body.health=p->health=100;body.height=56*FRACUNIT;
    p->ammo[0]=50;memcpy(p->maxammo,maxammo,sizeof(p->maxammo));
    p->weaponowned[0]=p->weaponowned[1]=1;p->readyweapon=1;p->pendingweapon=9;p->message="-";
    gameskill=sk_medium;gamemode=commercial;
    static sector_t sector;static subsector_t subsector;subsector.sector=&sector;body.subsector=&subsector;
}
static void print_state(int accepted) {
    player_t *p=players;
    printf("%d %d %d %d %d %d %d %d %d %d %d %d",accepted,sound_event,p->health,body.health,
        p->armorpoints,p->armortype,p->readyweapon,p->pendingweapon,p->bonuscount,p->itemcount,p->backpack,!!(body.flags&MF_SHADOW));
    for(int i=0;i<4;i++) printf(" %d",p->ammo[i]);
    for(int i=0;i<4;i++) printf(" %d",p->maxammo[i]);
    int weapons=0,cards=0;
    for(int i=0;i<9;i++) if(p->weaponowned[i]) weapons|=1<<i;
    for(int i=0;i<6;i++) if(p->cards[i]) cards|=1<<i;
    printf(" %d %d",weapons,cards);
    for(int i=0;i<6;i++) printf(" %d",p->powers[i]);
    printf(" %s\n",p->message);
}
/* LIGHTING */
int main(int argc,char **argv) {
    assert(argc==2);FILE *in=fopen(argv[1],"r");assert(in);reset();
    char line[1024];
    while(fgets(line,sizeof(line),in)) {
        char *op=strtok(line," \r\n");if(!op)continue;
        int a[16],n=0;char *token;
        while((token=strtok(NULL," \r\n"))) { assert(n<16);long v=strtol(token,NULL,10);assert(v>=INT_MIN&&v<=INT_MAX);a[n++]=(int)v; }
        player_t *p=players;int accepted=-1;removed=sound_event=0;
        if(!strcmp(op,"light")&&n==6) { printf("%d\n",light_choice(a[0],a[1],a[2],a[3],a[4],a[5]));continue; }
        if(!strcmp(op,"editor")&&n==1) {
            int found=0;
            for(int i=0;i<36;i++) if(pickup_metadata[i][0]==a[0]) {
                printf("%d %d %d %d\n",pickup_metadata[i][1],pickup_metadata[i][2],
                    pickup_metadata[i][3]/FRACUNIT,pickup_metadata[i][4]/FRACUNIT);found=1;break;
            }
            if(!found) puts("none");
            continue;
        }
        if(!strcmp(op,"think")&&n==1) {
            assert(a[0]==0||a[0]==1);p->playerstate=a[0];counter_trace=0;P_PlayerThink(p);
            for(int i=0;i<6;i++) printf("%d ",p->powers[i]);
            printf("%d %d %d %d %d\n",!!(body.flags&MF_SHADOW),p->bonuscount,
                p->damagecount,p->fixedcolormap,counter_trace);continue;
        }
        if(!strcmp(op,"counters")&&n==2) { p->damagecount=a[0];p->fixedcolormap=a[1]; }
        else if(!strcmp(op,"reset")&&n==0) reset();
        else if(!strcmp(op,"profile")&&n==2) { assert(a[0]>=0&&a[0]<5&&(a[1]==0||a[1]==1));gameskill=a[0];gamemode=a[1]; }
        else if(!strcmp(op,"base")&&n==10) {
            assert(a[4]>=0&&a[4]<9&&a[5]>=0&&a[5]<10);
            p->health=a[0];body.health=a[1];p->armorpoints=a[2];p->armortype=a[3];p->readyweapon=a[4];p->pendingweapon=a[5];
            p->bonuscount=a[6];p->itemcount=a[7];p->backpack=a[8];body.flags=a[9]?MF_SHADOW:0;
        } else if(!strcmp(op,"ammo")&&n==4) memcpy(p->ammo,a,sizeof(p->ammo));
        else if(!strcmp(op,"max")&&n==4) memcpy(p->maxammo,a,sizeof(p->maxammo));
        else if(!strcmp(op,"powers")&&n==6) memcpy(p->powers,a,sizeof(p->powers));
        else if(!strcmp(op,"weapons")&&n==1) { for(int i=0;i<9;i++) p->weaponowned[i]=((unsigned)a[0]>>i)&1; }
        else if(!strcmp(op,"cards")&&n==1) { for(int i=0;i<6;i++) p->cards[i]=((unsigned)a[0]>>i)&1; }
        else if(!strcmp(op,"giveammo")&&n==2) { assert(a[0]>=0&&a[0]<=4);accepted=P_GiveAmmo(p,a[0],a[1]); }
        else if(!strcmp(op,"giveweapon")&&n==2) { assert(a[0]>=0&&a[0]<9);accepted=P_GiveWeapon(p,a[0],a[1]); }
        else if(!strcmp(op,"givebody")&&n==1) accepted=P_GiveBody(p,a[0]);
        else if(!strcmp(op,"givearmor")&&n==1) accepted=P_GiveArmor(p,a[0]);
        else if(!strcmp(op,"givecard")&&n==1) { assert(a[0]>=0&&a[0]<6);P_GiveCard(p,a[0]);accepted=1; }
        else if(!strcmp(op,"givepower")&&n==1) { assert(a[0]>=0&&a[0]<6);accepted=P_GivePower(p,a[0]); }
        else if(!strcmp(op,"touch")&&n==6) {
            assert(a[0]>=0&&a[0]<36);special=(mobj_t){.sprite=a[0],.z=a[1],.flags=(a[4]?MF_DROPPED:0)|(a[5]?MF_COUNTITEM:0)};
            body.z=a[2];body.height=a[3];P_TouchSpecialThing(&special,&body);accepted=removed;
        } else abort();
        print_state(accepted);
    }
    fclose(in);return 0;
}

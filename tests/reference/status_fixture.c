/* Original status rules with a narrow single-player host. GPL-2.0-or-later. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
typedef int boolean;
typedef uint32_t angle_t;
typedef unsigned char byte;
#define true 1
#define false 0
#define TICRATE 35
#define NUMWEAPONS 9
#define MAXPLAYERS 4
#define ANG45 0x20000000u
#define ANG180 0x80000000u
#define CF_GODMODE 2
#define pw_invulnerability 0
#define pw_strength 1
#define pw_ironfeet 3
#define am_noammo 4
#define exe_chex 99
#define PU_CACHE 0
#define ST_Y 168
#define SHORT(x) (x)
/* CONSTANTS */
typedef struct { int x,y; angle_t angle; } mobj_t;
typedef struct {
    int health,damagecount,bonuscount,powers[6],weaponowned[9],attackdown,cheats;
    int readyweapon,ammo[4],cards[6];
    mobj_t *mo,*attacker;
} player_t;
static mobj_t body,attacker;
static player_t player={.health=100,.weaponowned={1,1},.mo=&body};
static player_t *plyr=&player;
static int st_faceindex,st_facecount,st_oldhealth=-1,st_randomnumber;
static boolean oldweaponsowned[9]={1,1};
static angle_t fixture_angle;
static angle_t R_PointToAngle2(int a,int b,int c,int d) { (void)a;(void)b;(void)c;(void)d;return fixture_angle; }
static int st_palette=-1,lu_palette,gameversion;
static byte palettes[14*768];
static void *W_CacheLumpNum(int a,int b) { (void)a;(void)b;return palettes; }
static void I_SetPalette(byte *p) { (void)p; }
typedef struct { int width,height,id; } patch_t;
typedef struct { int x,y,width,oldnum; int *num; boolean *on; patch_t **p; } st_number_t;
static patch_t minus={8,12,10}, *sttminus=&minus;
static byte *st_backing_screen;
static void I_Error(const char *msg,...) { fprintf(stderr,"%s\n",msg);exit(2); }
static void V_CopyRect(int a,int b,byte *c,int d,int e,int f,int g) { (void)a;(void)b;(void)c;(void)d;(void)e;(void)f;(void)g; }
static void V_DrawPatch(int x,int y,patch_t *p) { (void)y;printf(" %d:%d",x,p->id); }
static struct { int ammo; } weaponinfo[9]={{4},{0},{1},{0},{3},{2},{2},{4},{1}};
static struct { int *num; int data; } w_ready;
static int keyboxes[3];
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
/* FUNCTIONS */
#pragma GCC diagnostic pop
static void widget_selection(void) {
/* WIDGET_SELECTION */
}
static unsigned owned_mask(void) { unsigned mask=0;for(int i=0;i<9;i++)if(oldweaponsowned[i])mask|=1u<<i;return mask; }
int main(int argc,char **argv) {
    if(argc!=2)return 2;
    FILE *f=fopen(argv[1],"r");if(!f)return 2;
    char line[512],op[32];
    while(fgets(line,sizeof(line),f)) {
        if(sscanf(line,"%31s",op)!=1)continue;
        if(!strcmp(op,"palette")) {
            if(sscanf(line,"%*s %d %d %d %d",&player.damagecount,&player.bonuscount,&player.powers[1],&player.powers[3])!=4)return 2;
            ST_doPaletteStuff();printf("%d\n",st_palette);
        } else if(!strcmp(op,"num")) {
            int value,width,w; if(sscanf(line,"%*s %d %d %d",&value,&width,&w)!=3)return 2;
            patch_t patches[10],*ptrs[10];for(int i=0;i<10;i++){patches[i]=(patch_t){w,12,i};ptrs[i]=&patches[i];}
            int on=1;st_number_t n={44,171,width,0,&value,&on,ptrs};
            printf("num");STlib_drawNum(&n,1);puts("");
        } else if(!strcmp(op,"start")) {
            unsigned mask;if(sscanf(line,"%*s %u",&mask)!=1)return 2;
            st_faceindex=0;st_oldhealth=-1;
            for(int i=0;i<9;i++)oldweaponsowned[i]=!!(mask&(1u<<i));
            printf("%d %d %d %u\n",st_faceindex,st_facecount,st_oldhealth,owned_mask());
        } else if(!strcmp(op,"face")) {
            unsigned weapons,angle;long long bad;int god;
            if(sscanf(line,"%*s %d %d %d %d %u %d %d %u %lld %d",&player.health,&player.damagecount,&player.bonuscount,&player.powers[0],&weapons,&player.attackdown,&god,&angle,&bad,&st_randomnumber)!=10)return 2;
            player.cheats=god?CF_GODMODE:0;body.angle=angle;fixture_angle=(angle_t)bad;
            player.attacker=bad<0?NULL:&attacker;
            for(int i=0;i<9;i++)player.weaponowned[i]=!!(weapons&(1u<<i));
            ST_updateFaceWidget();st_oldhealth=player.health;
            printf("%d %d %d %u\n",st_faceindex,st_facecount,st_oldhealth,owned_mask());
        } else if(!strcmp(op,"widgets")) {
            unsigned mask;
            if(sscanf(line,"%*s %d %u %d %d %d %d",&player.readyweapon,&mask,&player.ammo[0],&player.ammo[1],&player.ammo[2],&player.ammo[3])!=6)return 2;
            for(int i=0;i<6;i++)player.cards[i]=!!(mask&(1u<<i));
            widget_selection();printf("%d %d %d %d\n",*w_ready.num,keyboxes[0],keyboxes[1],keyboxes[2]);
        } else return 2;
    }
    fclose(f);return 0;
}

/* Minimal host for pinned original bodies; no gameplay reimplementation. */
#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int boolean;
typedef struct { int floorheight, special; } sector_t;
typedef struct { sector_t *sector; } subsector_t;
typedef struct { subsector_t *subsector; int z; void *player; } mobj_t;
typedef struct { mobj_t *mo; int powers[1],secretcount,cheats,health; } player_t;
typedef struct { int special,flags,sidenum[2]; } line_t;
typedef struct { int toptexture,midtexture,bottomtexture; } side_t;
typedef struct { void *soundorg; } button_t;
typedef struct { char name1[9],name2[9]; int episode; } switchlist_t;
enum { shareware, registered, retail, commercial };
enum { sfx_swtchn, sfx_swtchx, top, middle, bottom, BUTTONTIME=35 };
enum { pw_ironfeet, CF_GODMODE=1, ML_SECRET=32, ga_nothing=0, ga_completed=1 };
#define arrlen(x) ((int)(sizeof(x)/sizeof((x)[0])))
#define DEH_String(x) (x)
static int switchlist[256],numswitches,gamemode,gameaction,secretexit,leveltime,totalsecret;
static side_t sides[1];
static button_t buttonlist[1];
static char trace[128];
static void I_Error(const char *fmt,...) { (void)fmt; abort(); }
static void S_StartSound(void *origin,int sound) { (void)origin; char buf[32];snprintf(buf,sizeof(buf)," s %d",sound);strcat(trace,buf); }
static void P_StartButton(line_t *line,int where,int texture,int time) { (void)line;(void)where;(void)texture;(void)time;abort(); }
static void P_DamageMobj(mobj_t *m,void *a,void *b,int damage) { (void)m;(void)a;(void)b;(void)damage;abort(); }
static int P_Random(void) { abort(); }
static char texture_names[128][9];
static int numtextures;
static int R_TextureNumForName(const char *name) {
    for(int i=0;i<numtextures;i++) if(!strcmp(texture_names[i],name)) return i;
    assert(numtextures<128);strcpy(texture_names[numtextures],name);return numtextures++;
}
/* ROUTINES */
static int next(void) { char *s=strtok(NULL," \r\n");assert(s);return (int)strtol(s,NULL,10); }
int main(int argc,char **argv) {
    assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char buf[16384];
    sector_t sector={0};subsector_t sub={&sector};mobj_t mo={&sub,0,NULL};player_t player={0};player.mo=&mo;
    while(fgets(buf,sizeof(buf),f)) {
        char *op=strtok(buf," \r\n");if(!op)continue;
        if(!strcmp(op,"secret")||!strcmp(op,"visit")) {
            mo.z=next();sector.floorheight=next();
            if(!strcmp(op,"secret")){sector.special=next();player.secretcount=next();}
            if(sector.special) P_PlayerInSpecialSector(&player);
            printf("%d %d\n",sector.special,player.secretcount);
        } else if(!strcmp(op,"total")) {
            int n=next();totalsecret=0;for(int i=0;i<n;i++)count_secret(next());printf("%d\n",totalsecret);
        } else if(!strcmp(op,"palette")) {
            int ep=next();gamemode=ep==1?shareware:ep==2?registered:commercial;numtextures=0;P_InitSwitchList();
            printf("%d",numswitches*2);for(int i=0;i<numswitches*2;i++)printf(" %s",texture_names[switchlist[i]]);puts("");
        } else if(!strcmp(op,"exit")) {
            int human=next(),side=next();line_t line={0};line.flags=next();line.special=next();
            sides[0].toptexture=next();sides[0].midtexture=next();sides[0].bottomtexture=next();
            int n=next();assert(n%2==0&&n<=256);numswitches=n/2;for(int i=0;i<n;i++)switchlist[i]=next();
            mo.player=human?&player:NULL;gameaction=ga_nothing;secretexit=true;trace[0]=0;
            P_UseSpecialLine(&mo,&line,side);
            printf("%d %d %d %d %d %d /%s\n",line.special,sides[0].toptexture,sides[0].midtexture,sides[0].bottomtexture,gameaction,secretexit,trace);
        } else abort();
    }
    fclose(f);return 0;
}

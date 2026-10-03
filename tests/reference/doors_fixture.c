/* Minimal host for unchanged T_MovePlane / T_VerticalDoor bodies.
   P_ChangeSector returns supplied replies; actor clipping is not stubbed parity.
   GPL-2.0-or-later. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <assert.h>
#include <stdbool.h>
typedef int32_t fixed_t;
typedef bool boolean;
typedef struct { int removed; } thinker_t;
typedef struct { fixed_t floorheight,ceilingheight; void *specialdata; int soundorg; } sector_t;
enum { ok, crushed, pastdest };
typedef int result_e;
enum { sfx_dorcls, sfx_doropn, sfx_bdcls };
#define TICRATE 35
/* TYPES */
static sector_t sector;
static vldoor_t door;
static unsigned mask,calls;
static char trace[512];static size_t used;
static void event(const char *format,...) {
    va_list args;va_start(args,format);
    int n=vsnprintf(trace+used,sizeof(trace)-used,format,args);va_end(args);
    assert(n>=0&&(size_t)n<sizeof(trace)-used);used+=(size_t)n;
}
static boolean P_ChangeSector(sector_t *s,boolean crush) {
    assert(calls<2);event(" c %d %d %d",s->floorheight,s->ceilingheight,crush);
    return (mask>>calls++)&1;
}
static void P_RemoveThinker(thinker_t *t) { t->removed=1;event(" r"); }
static void S_StartSound(void *origin,int sound) { assert(origin==&sector.soundorg);event(" s %d",sound); }
/* ROUTINES */
static void clear_trace(unsigned replies) {mask=replies;calls=0;used=0;trace[0]=0;}
static void dump_door(void) {
    printf("d %d %d %d %d %d %d %d %d %d %d /%s\n",door.type,sector.floorheight,sector.ceilingheight,
        door.speed,door.topheight,door.direction,door.topwait,door.topcountdown,door.thinker.removed,sector.specialdata!=NULL,trace);
}
int main(int argc,char **argv) {
    assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char line[512],op[32];int a,b,c,d,e,g,h,i,j;
    while(fgets(line,sizeof(line),f)) {
        int n=sscanf(line,"%31s %d %d %d %d %d %d %d %d %d",op,&a,&b,&c,&d,&e,&g,&h,&i,&j);
        if(n==9&&!strcmp(op,"plane")) {
            sector.floorheight=a;sector.ceilingheight=b;clear_trace(i);
            result_e r=T_MovePlane(&sector,c,d,e,g,h);
            printf("p %d %d %d /%s\n",r,sector.floorheight,sector.ceilingheight,trace);
        } else if(n==9&&!strcmp(op,"door")) {
            sector=(sector_t){.floorheight=b,.ceilingheight=c,.specialdata=&door};
            door=(vldoor_t){.type=a,.sector=&sector,.speed=d,.topheight=e,.direction=g,.topwait=h,.topcountdown=i};
            clear_trace(0);dump_door();
        } else if(n==2&&!strcmp(op,"tick")) {
            clear_trace(a);if(!door.thinker.removed)T_VerticalDoor(&door);dump_door();
        } else if(n==3&&!strcmp(op,"height")) {
            sector.floorheight=a;sector.ceilingheight=b;clear_trace(0);dump_door();
        } else abort();
    }
    fclose(f);return 0;
}

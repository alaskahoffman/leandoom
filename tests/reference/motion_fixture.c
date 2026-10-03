/* Test-only environment for unchanged upstream routines. Not an engine.
 * Only keyboard movement/fire/use and unobstructed player physics are supported.
 * P_CalcHeight can also be called alone with its non-live recovery branch.
 * Unsupported callbacks abort. State identifiers are fixture-local ordinals.
 */
#include <assert.h>
#include <stdbool.h>
#define FRACUNIT 65536
#define ANGLETOFINESHIFT 19
#define MAXMOVE (30*FRACUNIT)
#define STOPSPEED 0x1000
#define FRICTION 0xe800
#define CF_NOMOMENTUM 1
#define MF_MISSILE 0x10000
#define MF_CORPSE 0x100000
#define MF_SKULLFLY 0x1000000
#define MF_NOGRAVITY 512
#define MF_NOCLIP 0x1000
#define MF_FLOAT 0x4000
#define MF_INFLOAT 0x200000
#define GRAVITY FRACUNIT
#define FLOATSPEED (FRACUNIT*4)
#define VIEWHEIGHT (41*FRACUNIT)
#define MAXBOB 0x100000
#define FINEMASK (FINEANGLES-1)
#define PST_LIVE 0
#define exe_ultimate 1
#define sfx_oof 0
#define S_PLAY 0
#define S_PLAY_RUN1 1
typedef int boolean;
typedef struct { signed char forwardmove, sidemove; short angleturn;
                 unsigned char buttons, chatchar, consistancy; } ticcmd_t;
_Static_assert(CHAR_BIT == 8 && sizeof(short) == 2, "ticcmd widths");
typedef struct player_s player_t;
typedef struct { int ordinal; } state_t;
typedef struct { int spawnstate; } mobjinfo_t;
typedef struct { int ceilingpic; fixed_t floorheight; } sector_t;
typedef struct { sector_t *sector; } subsector_t;
typedef struct { sector_t *backsector; } line_t;
typedef struct mobj_s {
    fixed_t x,y,momx,momy,momz,z,floorz;
    angle_t angle;
    int flags;
    player_t *player;
    state_t *state;
    mobjinfo_t *info;
    subsector_t *subsector;
    struct mobj_s *target;
    fixed_t ceilingz,height;
} mobj_t;
struct player_s { mobj_t *mo; ticcmd_t cmd; int cheats;
                  fixed_t viewheight,deltaviewheight,viewz,bob; int playerstate; };
static state_t states[5];
static line_t *ceilingline;
static int skyflatnum;
static boolean onground;
static int leveltime,gameversion,landing_count;
static mobj_t body;
static player_t player;
static fixed_t attempts[2][2];
static int attempt_count;
static void P_SetMobjState(mobj_t *mo, int state) {
    assert(state >= 0 && state < 5); mo->state = &states[state];
}
static boolean P_TryMove(mobj_t *mo, fixed_t x, fixed_t y) {
    assert(mo == &body && (mo->flags & ~MF_NOGRAVITY) == 0 && attempt_count < 2);
    attempts[attempt_count][0] = x; attempts[attempt_count++][1] = y;
    mo->x = x; mo->y = y; return true;
}
static void P_SlideMove(mobj_t *mo) { (void)mo; abort(); }
static void P_RemoveMobj(mobj_t *mo) { (void)mo; abort(); }
static void P_ExplodeMissile(mobj_t *mo) { (void)mo; abort(); }
static fixed_t P_AproxDistance(fixed_t x, fixed_t y) { (void)x; (void)y; abort(); }
static void S_StartSound(mobj_t *mo, int sound) {
    assert(mo == &body && sound == sfx_oof); ++landing_count;
}

#define NUMKEYS 256
#define MAX_JOY_BUTTONS 20
#define BACKUPTICS 128
#define GS_LEVEL 1
#define BT_ATTACK 1
#define BT_USE 2
#define BT_CHANGE 4
#define BT_WEAPONSHIFT 3
#define BT_SPECIAL 128
#define BTS_PAUSE 1
#define BTS_SAVEGAME 2
#define BTS_SAVESHIFT 2
#define MAXPLMOVE (forwardmove[1])
#define SLOWTURNTICS 6
#define arrlen(x) ((int)(sizeof(x)/sizeof((x)[0])))
static int gamekeydown[NUMKEYS], mousebuttons[1], joybuttons[1];
static int key_up=0, key_down=1, key_left=2, key_right=3,
           key_strafeleft=4, key_straferight=5, key_strafe=6,
           key_speed=7, key_fire=8, key_use=9;
static int weapon_key_storage[8] = {20,21,22,23,24,25,26,27};
static int *weapon_keys[] = { &weapon_key_storage[0], &weapon_key_storage[1],
    &weapon_key_storage[2], &weapon_key_storage[3], &weapon_key_storage[4],
    &weapon_key_storage[5], &weapon_key_storage[6], &weapon_key_storage[7] };
static int mousebstrafe,joybstrafe,joybspeed,mousebspeed,mousebturnright,mousebturnleft;
static int joybstrafeleft,mousebstrafeleft,joybstraferight,mousebstraferight;
static int mousebfire,joybfire,joybuse,mousebuse,mousebforward,mousebbackward;
static int use_analog,joyxmove,joyymove,joystrafemove;
static int joystick_move_sensitivity,joystick_turn_sensitivity;
static int mousex,mousey,dclick_use,dclicks,dclickstate,dclicktime;
static int dclicks2,dclickstate2,dclicktime2,testcontrols_mousespeed;
static int gamestate=GS_LEVEL,next_weapon,sendpause,sendsave,savegameslot,lowres_turn;
static int consistancy[1][BACKUPTICS],consoleplayer,turnheld,ticdup=1;
static int HU_dequeueChatChar(void) { return 0; }
static int G_NextWeapon(int direction) { (void)direction; abort(); }

/* REFERENCE_FUNCTIONS */

static void reset_motion(void) {
    memset(&body, 0, sizeof(body)); memset(&player, 0, sizeof(player));
    body.player = &player; player.mo = &body; body.state = &states[S_PLAY];
    body.height=56*FRACUNIT; body.ceilingz=128*FRACUNIT;
    player.viewheight=VIEWHEIGHT; player.playerstate=PST_LIVE;
    turnheld = 0; attempt_count = 0;
    landing_count=0; onground=false; leveltime=0;
}
static void print_body_fields(void) {
    printf("%d %d %d %d %u %td %d", body.x,body.y,body.momx,body.momy,
           body.angle,body.state-states,attempt_count);
    for (int i=0; i<attempt_count; ++i) printf(" %d %d",attempts[i][0],attempts[i][1]);
}
static void print_body(void) { print_body_fields(); putchar('\n'); }
static void print_physics(void) {
    print_body_fields();
    printf(" | %d %d %d %d %d %d %d %d %d %d %d\n",
        body.z,body.momz,body.floorz,body.ceilingz,body.height,
        !!(body.flags&MF_NOGRAVITY),player.viewheight,player.deltaviewheight,
        player.viewz,player.bob,landing_count);
}
static void print_cmd(void) {
    printf("%d %d %d %u %d",player.cmd.forwardmove,player.cmd.sidemove,
           player.cmd.angleturn,player.cmd.buttons,turnheld);
}
static int motion_command(const char *line) {
    char op[16]; int32_t a[9]={0};
    int n=sscanf(line,"%15s %"SCNd32" %"SCNd32" %"SCNd32" %"SCNd32
                 " %"SCNd32" %"SCNd32" %"SCNd32" %"SCNd32" %"SCNd32,
                 op,&a[0],&a[1],&a[2],&a[3],&a[4],&a[5],&a[6],&a[7],&a[8]);
    attempt_count = 0; landing_count=0;
    if (n==1 && !strcmp(op,"reset")) { reset_motion(); puts("reset"); }
    else if (n==2 && !strcmp(op,"held")) { turnheld=a[0]; puts("held"); }
    else if (n==10 && !strcmp(op,"body")) {
        assert(a[7]>=0 && a[7]<5 && (a[8]==0 || a[8]==1));
        body.x=a[0]; body.y=a[1]; body.momx=a[2]; body.momy=a[3];
        body.angle=(angle_t)a[4]; body.z=a[5]; body.floorz=a[6];
        body.state=&states[a[7]]; player.cheats=a[8] ? CF_NOMOMENTUM : 0;
        body.momz=0; body.ceilingz=128*FRACUNIT; body.height=56*FRACUNIT; body.flags=0;
        print_body();
    } else if (n==3 && (!strcmp(op,"key") || !strcmp(op,"tick"))) {
        assert(a[0]>=0 && a[0]<1024 && a[1]>=1 && a[1]<=9);
        memset(gamekeydown,0,sizeof(gamekeydown));
        for (int i=0; i<10; ++i) gamekeydown[i]=(a[0]>>i)&1;
        ticdup=a[1]; G_BuildTiccmd(&player.cmd,0); print_cmd();
        if (!strcmp(op,"tick")) {
            P_MovePlayer(&player); P_XYMovement(&body); printf(" | "); print_body();
        } else putchar('\n');
    } else if (n==4 && (!strcmp(op,"move") || !strcmp(op,"xy"))) {
        assert(a[0]>=-128 && a[0]<=127 && a[1]>=-128 && a[1]<=127 && a[2]>=-32768 && a[2]<=32767);
        player.cmd.forwardmove=a[0]; player.cmd.sidemove=a[1]; player.cmd.angleturn=a[2];
        if (!strcmp(op,"move")) P_MovePlayer(&player); else P_XYMovement(&body);
        print_body();
    } else if (n==3 && !strcmp(op,"thrust")) {
        P_Thrust(&player,(angle_t)a[0],a[1]); print_body();
    } else if (n==5 && !strcmp(op,"vertical")) {
        assert(a[3]==0 || a[3]==1);
        body.momz=a[0]; body.ceilingz=a[1]; body.height=a[2];
        body.flags=a[3] ? MF_NOGRAVITY : 0; print_physics();
    } else if (n==5 && !strcmp(op,"view")) {
        player.viewheight=a[0]; player.deltaviewheight=a[1];
        player.viewz=a[2]; player.bob=a[3]; print_physics();
    } else if (n==3 && !strcmp(op,"space")) {
        body.floorz=a[0]; body.ceilingz=a[1]; print_physics();
    } else if (n==1 && !strcmp(op,"zmove")) {
        P_ZMovement(&body); print_physics();
    } else if (n==4 && !strcmp(op,"height")) {
        assert((a[1]==0 || a[1]==1) && (a[2]==0 || a[2]==1));
        leveltime=a[0]; onground=a[1]; player.playerstate=a[2] ? PST_LIVE : 1;
        P_CalcHeight(&player); print_physics();
    } else if (n==4 && !strcmp(op,"physics")) {
        assert(a[0]>=0 && a[0]<1024 && a[1]>=1 && a[1]<=9);
        memset(gamekeydown,0,sizeof(gamekeydown));
        for (int i=0; i<10; ++i) gamekeydown[i]=(a[0]>>i)&1;
        ticdup=a[1]; leveltime=a[2]; player.playerstate=PST_LIVE;
        G_BuildTiccmd(&player.cmd,0); print_cmd();
        P_MovePlayer(&player); P_CalcHeight(&player);
        if (body.momx || body.momy) P_XYMovement(&body);
        if (body.z!=body.floorz || body.momz) P_ZMovement(&body);
        printf(" | "); print_physics();
    } else return 0;
    return 1;
}

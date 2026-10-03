/* Combined live-player movement, using the real collision/slide functions. */
#define MAXMOVE (30*FRACUNIT)
#define STOPSPEED 0x1000
#define FRICTION 0xe800
#define CF_NOMOMENTUM 1
#define MF_CORPSE 0x100000
#define MF_NOGRAVITY 512
#define MF_INFLOAT 0x200000
#define GRAVITY FRACUNIT
#define FLOATSPEED (4*FRACUNIT)
#define VIEWHEIGHT (41*FRACUNIT)
#define MAXBOB 0x100000
#define FINEMASK (FINEANGLES-1)
#define PST_LIVE 0
#define exe_ultimate 1
#define sfx_oof 0
#define S_PLAY 0
#define S_PLAY_RUN1 1
typedef struct { signed char forwardmove,sidemove; short angleturn; } ticcmd_t;
struct player_s { mobj_t *mo; ticcmd_t cmd; int cheats;
    fixed_t viewheight,deltaviewheight,viewz,bob; int playerstate;
    int health,armorpoints,armortype,ammo[4],maxammo[4],weaponowned[9],readyweapon,pendingweapon;
    int cards[6],powers[6],backpack,bonuscount,itemcount; const char *message; };
static player_t physical_player;
static int leveltime,gameversion,landing_count,world_slides,skyflatnum;
static boolean onground;
static void P_RemoveMobj(mobj_t *mo) {
    assert(mo>=things && mo<things+thing_count && !mo->removed);
    P_UnsetThingPosition(mo);mo->removed=1;
}
static void P_ExplodeMissile(mobj_t *mo) { (void)mo;abort(); }
static void pickup_sound(int sound);
static void S_StartSound(mobj_t *mo,int sound) {
    if(!mo) { pickup_sound(sound);return; }
    assert(mo==physical_player.mo && sound==sfx_oof);++landing_count;
}
static void world_slide(mobj_t *mo) { ++world_slides;P_SlideMove(mo); }
#define P_TryMove slide_try
#define P_SlideMove world_slide
/* WORLD_FUNCTIONS */
#undef P_TryMove
#undef P_SlideMove

static int world_command(const char *op,int32_t *a,int n) {
    if(!strcmp(op,"physical") && n==8) {
        assert(a[0]>=0 && a[0]<thing_count && a[3]>=0 && a[3]<5);
        mobj_t *t=&things[a[0]];
        physical_player=(player_t){.mo=t,.cheats=a[4]?CF_NOMOMENTUM:0,
            .viewheight=a[6],.deltaviewheight=a[7]};
        t->player=&physical_player;t->angle=(unsigned int)a[1];t->momz=a[2];t->state=&states[a[3]];
        if(a[5]) t->flags|=MF_NOGRAVITY;else t->flags&=~MF_NOGRAVITY;
        puts("physical");
    } else if((!strcmp(op,"worldxy") || !strcmp(op,"worldtick")) && n==5) {
        assert(a[0]>=0 && a[0]<thing_count && physical_player.mo==&things[a[0]] && effect_mode==0);
        assert(a[1]>=-128 && a[1]<=127 && a[2]>=-128 && a[2]<=127 && a[3]>=-32768 && a[3]<=32767);
        player_t *p=&physical_player;mobj_t *t=p->mo;
        p->cmd=(ticcmd_t){a[1],a[2],a[3]};leveltime=a[4];
        slide_attempt_count=slide_path_count=cross_count=landing_count=world_slides=0;
        if(!strcmp(op,"worldxy")) P_XYMovement(t);
        else {
            P_MovePlayer(p);P_CalcHeight(p);
            if(t->momx || t->momy) P_XYMovement(t);
            if(t->z!=t->floorz || t->momz) P_ZMovement(t);
        }
        print_scene();
        printf(" | %d %d %d %u %td %d %d %d %d %d | %d",t->momx,t->momy,t->momz,t->angle,
            t->state-states,p->viewheight,p->deltaviewheight,p->viewz,p->bob,landing_count,slide_attempt_count);
        for(int i=0;i<slide_attempt_count;i++) for(int j=0;j<4;j++) printf(" %d",slide_attempts[i][j]);
        printf(" | %d | %d",world_slides,cross_count);
        for(int i=0;i<cross_count;i++) for(int j=0;j<5;j++) printf(" %d",cross_events[i][j]);
        putchar('\n');
    } else return 0;
    return 1;
}

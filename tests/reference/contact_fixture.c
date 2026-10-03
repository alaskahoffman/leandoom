/* Real PIT_CheckThing/P_CheckPosition/P_TryMove call the real pickup routines.
 * P_RemoveMobj performs original unlinking; thinker deletion/respawn/audio are
 * outside this fixture. Removed mobj storage/bnext remain valid during traversal. */
typedef int ammotype_t;
typedef int weapontype_t;
typedef int card_t;
#define NUMAMMO 4
#define BONUSADD 6
#define MAXHEALTH 100
#define INVULNTICS 1050
#define INVISTICS 2100
#define INFRATICS 4200
#define IRONTICS 2100
#define MF_SHADOW 0x40000
#define MF_DROPPED 0x20000
#define MF_COUNTITEM 0x800000
enum { am_clip,am_shell,am_cell,am_misl,am_noammo };
enum { wp_fist,wp_pistol,wp_shotgun,wp_chaingun,wp_missile,wp_plasma,wp_bfg,wp_chainsaw,wp_supershotgun };
enum { it_bluecard,it_yellowcard,it_redcard,it_blueskull,it_yellowskull,it_redskull };
enum { pw_invulnerability,pw_strength,pw_invisibility,pw_ironfeet,pw_allmap,pw_infrared };
enum { sk_baby,sk_easy,sk_medium,sk_hard,sk_nightmare };
enum { sfx_itemup=1,sfx_wpnup,sfx_getpow };
enum { exe_doom_1_2=0,commercial=1 };
#define DEH_String(x) (x)
#define players (&physical_player)
static int gameskill=sk_medium,gamemode=commercial,netgame,deathmatch,consoleplayer;
/* DECLARATIONS */
/* CONSTANTS */
static int touch_sound,touch_count;
static struct {int id,removed,sound;const char *message;} touch_events[4096];
static void pickup_sound(int sound) { touch_sound=sound; }
#define P_TouchSpecialThing pickup_effect
/* FUNCTIONS */
#undef P_TouchSpecialThing
static void P_TouchSpecialThing(mobj_t *item,mobj_t *toucher) {
    assert(toucher==physical_player.mo && touch_count<4096);
    touch_sound=0;pickup_effect(item,toucher);
    touch_events[touch_count].id=(int)(item-things);
    touch_events[touch_count].removed=item->removed;
    touch_events[touch_count].sound=touch_sound;
    touch_events[touch_count++].message=physical_player.message;
}
static int contact_command(const char *op,int32_t *a,int n) {
    player_t *p=&physical_player;
    if(!strcmp(op,"collector") && n==5) {
        assert(a[0]>=0&&a[0]<thing_count);mobj_t *t=&things[a[0]];
        p->mo=t;t->player=p;t->flags=(t->flags&~MF_PICKUP)|(a[4]?MF_PICKUP:0);
        p->health=t->health=a[1];p->armorpoints=p->armortype=p->backpack=p->bonuscount=p->itemcount=0;
        memset(p->ammo,0,sizeof(p->ammo));p->ammo[0]=50;memcpy(p->maxammo,maxammo,sizeof(p->maxammo));
        memset(p->weaponowned,0,sizeof(p->weaponowned));p->weaponowned[0]=p->weaponowned[1]=1;
        memset(p->cards,0,sizeof(p->cards));memset(p->powers,0,sizeof(p->powers));
        p->readyweapon=1;p->pendingweapon=9;p->message="-";gameskill=a[2];gamemode=a[3];gameversion=exe_ultimate;
        touch_count=0;puts("collector");
    } else if(!strcmp(op,"item")&&n==5) {
        assert(a[0]>=0&&a[0]<thing_count&&a[1]>=0&&a[1]<36);mobj_t *t=&things[a[0]];
        t->sprite=a[1];t->z=a[2];t->flags|=MF_SPECIAL|(a[3]?MF_DROPPED:0)|(a[4]?MF_COUNTITEM:0);puts("item");
    } else if(!strcmp(op,"collection")&&n==0) {
        printf("%d %d %d %d %d %d %d %d %d %d",p->health,p->mo->health,p->armorpoints,p->armortype,
            p->readyweapon,p->pendingweapon,p->bonuscount,p->itemcount,p->backpack,!!(p->mo->flags&MF_SHADOW));
        for(int i=0;i<4;i++)printf(" %d",p->ammo[i]);
        for(int i=0;i<4;i++)printf(" %d",p->maxammo[i]);
        int weapons=0,cards=0;
        for(int i=0;i<9;i++)if(p->weaponowned[i])weapons|=1<<i;
        for(int i=0;i<6;i++)if(p->cards[i])cards|=1<<i;
        printf(" %d %d",weapons,cards);
        for(int i=0;i<6;i++)printf(" %d",p->powers[i]);
        printf(" %s | %d",p->message,thing_count);
        for(int i=0;i<thing_count;i++)printf(" %d",things[i].removed);
        printf(" | %d",touch_count);
        for(int i=0;i<touch_count;i++)printf(" %d %d %d %s",touch_events[i].id,touch_events[i].removed,touch_events[i].sound,touch_events[i].message);
        putchar('\n');
    } else return 0;
    return 1;
}

/* Unchanged non-crushing P_ChangeSector and PIT_ChangeSector. Gib state has
 * no action; observe its request. Removal uses original sector/block unlinking.
 * Damage, blood spawning and RNG abort if the excluded crush branch is called. */
/* FLAGS */
static boolean nofit,crushchange;
static state_t gibs_state;
static int sector_visits[64],sector_nvisits,sector_events[128],sector_nevents;
#define S_GIBS 100
#define MT_BLOOD 100
static void sector_gib(mobj_t *t,int state) {
    assert(state==S_GIBS && sector_nevents<128);t->state=&gibs_state;
    sector_events[sector_nevents++]=(int)(t-things)*2;
}
static void sector_remove(mobj_t *t) {
    assert(sector_nevents<128);sector_events[sector_nevents++]=(int)(t-things)*2+1;P_RemoveMobj(t);
}
static mobj_t *P_SpawnMobj(int x,int y,int z,int type) { (void)x;(void)y;(void)z;(void)type;abort(); }
static int P_SubRandom(void) { abort(); }
#define P_SetMobjState sector_gib
#define P_RemoveMobj sector_remove
/* PIT */
#undef P_SetMobjState
#undef P_RemoveMobj
static boolean sector_visit(mobj_t *t) {
    assert(sector_nvisits<64);sector_visits[sector_nvisits++]=(int)(t-things);
    /* Fixture query visitation buffers are per-query, not global history. */
    nlines=nthings=0;
    return PIT_ChangeSector(t);
}
#define PIT_ChangeSector sector_visit
/* CHANGE */
#undef PIT_ChangeSector
static void sector_bounds(int *bbox,sector_t *sector) {
    int block;
    /* BOUNDS */
}
static int sector_command(const char *op,int32_t *a,int n) {
    if(!strcmp(op,"bounds") && n==8) {
        int ox=bmaporgx,oy=bmaporgy,w=bmapwidth,h=bmapheight;sector_t sector={0};
        bmaporgx=(int32_t)((uint32_t)a[4]*65536u);bmaporgy=(int32_t)((uint32_t)a[5]*65536u);
        bmapwidth=a[6];bmapheight=a[7];sector_bounds(a,&sector);
        printf("%d %d %d %d\n",sector.blockbox[BOXLEFT],sector.blockbox[BOXRIGHT],sector.blockbox[BOXBOTTOM],sector.blockbox[BOXTOP]);
        bmaporgx=ox;bmaporgy=oy;bmapwidth=w;bmapheight=h;
    } else if(!strcmp(op,"sectoractor") && n==4) {
        assert(a[0]>=0&&a[0]<thing_count);mobj_t *t=&things[a[0]];t->health=a[1];
        t->flags=(t->flags&~(MF_SHOOTABLE|MF_DROPPED))|(a[2]?MF_SHOOTABLE:0)|(a[3]?MF_DROPPED:0);
        puts("sectoractor");
    } else if(!strcmp(op,"change") && n==5) {
        assert(use_world);player_t *old[64];
        for(int i=0;i<thing_count;i++) {old[i]=things[i].player;if(i!=a[4])things[i].player=NULL;}
        sector_t sector={.blockbox={a[3],a[2],a[0],a[1]}};
        sector_nvisits=sector_nevents=0;clip_supplied=0;gameversion=exe_ultimate;
        int blocked=P_ChangeSector(&sector,false);
        printf("%d | %d",blocked,sector_nvisits);
        for(int i=0;i<sector_nvisits;i++)printf(" %d",sector_visits[i]);
        printf(" | %d",sector_nevents);for(int i=0;i<sector_nevents;i++)printf(" %d",sector_events[i]);
        printf(" | %d",thing_count);
        for(int i=0;i<thing_count;i++) {
            mobj_t *t=&things[i];t->player=old[i];
            printf(" %d %d %d %d %d %d %d",t->health,!!(t->flags&MF_SOLID),!!(t->flags&MF_SHOOTABLE),!!(t->flags&MF_DROPPED),t->state==&gibs_state,t->radius,t->removed);
        }
        printf(" | ");print_scene();putchar('\n');
    } else if(!strcmp(op,"actormeta") && n==1) {
        size_t i;
        for(i=0;i<sizeof(actor_meta)/sizeof(*actor_meta);i++) if(actor_meta[i][0]==a[0]) {
            int f=actor_meta[i][2];printf("%d %d %d %d\n",actor_meta[i][1],!!(f&MF_SHOOTABLE),!!(f&MF_NOBLOCKMAP),!!(f&MF_NOSECTOR));break;
        }
        if(i==sizeof(actor_meta)/sizeof(*actor_meta))puts("none");
    } else return 0;
    return 1;
}

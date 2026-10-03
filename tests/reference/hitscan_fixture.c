/* Unchanged aim/shoot bodies; callbacks record requests, not effect/damage parity. */
#define SCREENWIDTH 320
#define SCREENHEIGHT 200
#define MF_NOBLOOD 0x80000
static mobj_t *shootthing,*linetarget;
static fixed_t shootz,attackrange,aimslope,topslope,bottomslope,bulletslope;
static int la_damage;
static char shot_events[8192];
static void shot_event(char kind,int a,int b,int c,int d) {
    char text[128];snprintf(text,sizeof(text)," %c %d %d %d %d",kind,a,b,c,d);
    assert(strlen(shot_events)+strlen(text)<sizeof(shot_events));strcat(shot_events,text);
}
static void shot_special(mobj_t *who,line_t *line){assert(who==shootthing);shot_event('s',(int)(line-lines),0,0,0);}
static void shot_puff(fixed_t x,fixed_t y,fixed_t z){shot_event('p',x,y,z,0);}
static void shot_blood(fixed_t x,fixed_t y,fixed_t z,int damage){shot_event('b',x,y,z,damage);}
static void shot_damage(mobj_t *target,mobj_t *inflictor,mobj_t *source,int damage){assert(inflictor==shootthing&&source==shootthing);shot_event('d',(int)(target-things),damage,0,0);}
static mobj_t *P_SubstNullMobj(mobj_t *thing){assert(thing);return thing;}
#define P_ShootSpecialLine shot_special
#define P_SpawnPuff shot_puff
#define P_SpawnBlood shot_blood
#define P_DamageMobj shot_damage
#define FixedDiv checked_path_div
/* HIT_CALLBACKS */
#undef FixedDiv
#undef P_ShootSpecialLine
#undef P_SpawnPuff
#undef P_SpawnBlood
#undef P_DamageMobj
static boolean aim_callback(intercept_t *hit){current_path.visited[current_path.visit_count++]=*hit;return PTR_AimTraverse(hit);}
static boolean shoot_callback(intercept_t *hit){current_path.visited[current_path.visit_count++]=*hit;return PTR_ShootTraverse(hit);}
#define PTR_AimTraverse aim_callback
#define PTR_ShootTraverse shoot_callback
#define P_PathTraverse call_path
/* HIT_ENTRIES */
#undef P_PathTraverse
#undef PTR_AimTraverse
#undef PTR_ShootTraverse
/* BULLET_SLOPE */
static int hitscan_command(const char *op,int32_t *a,int n){
    if(!strcmp(op,"shootmeta")&&n==5){
        assert(a[0]>=0&&a[0]<thing_count);mobj_t *t=&things[a[0]];
        t->flags=(t->flags&~(MF_SHOOTABLE|MF_NOBLOOD))|(a[1]?MF_SHOOTABLE:0)|(a[2]?MF_NOBLOOD:0);t->z=a[3];t->height=a[4];puts("shootmeta");
    }else if(!strcmp(op,"skyline")&&n==3){
        assert(a[0]>=0&&a[0]<line_count);skyflatnum=7;line_t *l=&lines[a[0]];
        l->frontsector->ceilingpic=a[1]?7:0;if(l->backsector)l->backsector->ceilingpic=a[2]?7:0;puts("skyline");
    }else if(!strcmp(op,"aim")&&n==3){
        assert(a[0]>=0&&a[0]<thing_count&&a[2]>0);
        int slope=P_AimLineAttack(&things[a[0]],(unsigned)a[1],a[2]);
        printf("%d %td | ",slope,linetarget?linetarget-things:-1);print_path(&current_path);puts("");
    }else if(!strcmp(op,"shoot")&&n==5){
        assert(a[0]>=0&&a[0]<thing_count&&a[2]>0);shot_events[0]=0;skyflatnum=7;
        P_LineAttack(&things[a[0]],(unsigned)a[1],a[2],a[3],a[4]);
        printf("%s | ",shot_events);print_path(&current_path);puts("");
    }else if(!strcmp(op,"bulletslope")&&n==2){
        assert(a[0]>=0&&a[0]<thing_count);things[a[0]].angle=(unsigned)a[1];P_BulletSlope(&things[a[0]]);printf("%d\n",bulletslope);
    }else return 0;
    return 1;
}

/* Actual use path routines; dispatch and sfx_noway are requests recorded here.
 * Scrolling list initialization/update blocks are unchanged original C.
 * GPL-2.0-or-later. */
#define USERANGE (64*FRACUNIT)
#define sfx_noway 999
static mobj_t *usething;
static int use_action,use_line,use_side;
static void record_use_sound(mobj_t *thing,int sound) {
    assert(thing==usething && sound==sfx_noway);use_action=1;
}
static void P_UseSpecialLine(mobj_t *thing,line_t *line,int side) {
    assert(thing==usething);use_action=2;use_line=(int)(line-lines);use_side=side;
}
#define S_StartSound record_use_sound
/* USE_TRAVERSE */
#undef S_StartSound
static boolean use_callback(intercept_t *hit) {
    assert(current_path.visit_count<128);
    current_path.visited[current_path.visit_count++]=*hit;
    return PTR_UseTraverse(hit);
}
#define PTR_UseTraverse use_callback
#define P_PathTraverse call_path
/* USE_LINES */
#undef P_PathTraverse
#undef PTR_UseTraverse

typedef struct {int special,sidenum[2];} scroll_line_t;
typedef struct {fixed_t textureoffset;} scroll_side_t;
static scroll_line_t scroll_lines[128],*linespeciallist[64];
static scroll_side_t sides[64];
static int scroll_count,side_count,numlinespecials;
#define MAXLINEANIMS 64
static int NumScrollers(void) {return scroll_count;}
static void scroll_spawn(void) {
    int i,numlines=scroll_count;scroll_line_t *lines=scroll_lines;
    /* SCROLL_SPAWN */
}
static void scroll_tick(void) {
    int i;scroll_line_t *line;
    /* SCROLL_TICK */
}
static void scroll_print(void) {
    printf("%d",numlinespecials);
    for(int i=0;i<numlinespecials;i++)printf(" %td",linespeciallist[i]-scroll_lines);
    printf(" | %d",side_count);
    for(int i=0;i<side_count;i++)printf(" %d",sides[i].textureoffset);
    putchar('\n');
}
static int use_command(const char *op,int32_t *a,int n) {
    if(!strcmp(op,"use") && n==3) {
        mobj_t thing={.x=a[0],.y=a[1],.angle=(unsigned)a[2]};player_t player={.mo=&thing};
        use_action=0;use_line=use_side=-1;P_UseLines(&player);
        printf("%d %d %d | ",use_action,use_line,use_side);print_path(&current_path);putchar('\n');
    } else if(!strcmp(op,"scrollreset")&&n==0) {
        scroll_count=side_count=numlinespecials=0;puts("scrollreset");
    } else if(!strcmp(op,"scrollside")&&n==1) {
        assert(side_count<64);sides[side_count++].textureoffset=a[0];puts("scrollside");
    } else if(!strcmp(op,"scrollline")&&n==2) {
        assert(scroll_count<128 && a[1]>=0 && a[1]<side_count);
        scroll_lines[scroll_count++]=(scroll_line_t){.special=a[0],.sidenum={a[1],-1}};puts("scrollline");
    } else if(!strcmp(op,"scrollspecial")&&n==2) {
        assert(a[0]>=0&&a[0]<scroll_count);scroll_lines[a[0]].special=a[1];puts("scrollspecial");
    } else if(!strcmp(op,"scrollspawn")&&n==0) {scroll_spawn();scroll_print();}
    else if(!strcmp(op,"scrolltick")&&n==0) {scroll_tick();scroll_print();}
    else return 0;
    return 1;
}

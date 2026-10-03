/* Read-only path callbacks and bounded slide traces. No overrun emulation. */
typedef unsigned int angle_t;
typedef struct { fixed_t x,y,dx,dy; } divline_t;
typedef struct { fixed_t frac; boolean isaline; union { line_t *line; mobj_t *thing; } d; } intercept_t;
typedef boolean (*traverser_t)(intercept_t *);
#define FINEANGLES 8192
#define SLOPERANGE 2048
#define ANG90 0x40000000
#define ANG180 0x80000000
#define ANG270 0xc0000000
#define ANGLETOFINESHIFT 19
#define MAPBLOCKSIZE (128*FRACUNIT)
#define MAPBTOFRAC 7
#define PT_ADDLINES 1
#define PT_ADDTHINGS 2
#define PT_EARLYOUT 4
static fixed_t viewx,viewy;
static divline_t trace;
static intercept_t intercepts[128],*intercept_p;
static boolean earlyout;
static mobj_t *slidemo;
static fixed_t bestslidefrac,secondslidefrac,tmxmove,tmymove;
static line_t *bestslideline,*secondslideline;
typedef struct {
    int completed,block_count,raw_count,visit_count;
    divline_t trace;
    int blocks[128][3];
    intercept_t raw[128],visited[128];
} path_record_t;
static path_record_t current_path,slide_paths[12];
static int slide_path_count,slide_attempt_count,slide_attempts[20][4],path_stop;
static void print_scene(void);
static void I_Error(const char *s,...) { (void)s; abort(); }
static void InterceptsOverrun(int index,intercept_t *hit) {
    assert(index<128 && current_path.raw_count<128);
    current_path.raw[current_path.raw_count++]=*hit;
}
static fixed_t checked_path_div(fixed_t a,fixed_t b) {
    assert(a!=INT_MIN && b!=INT_MIN);return FixedDiv(a,b);
}
static int checked_path_abs(int a) { assert(a!=INT_MIN);return abs(a); }
#define FixedDiv checked_path_div
#define abs checked_path_abs

/* PATH_FUNCTIONS */

static boolean path_lines(int x,int y,boolean(*fn)(line_t*)) {
    assert(current_path.block_count<128);int *v=current_path.blocks[current_path.block_count++];
    v[0]=1;v[1]=x;v[2]=y;return P_BlockLinesIterator(x,y,fn);
}
static boolean path_things(int x,int y,boolean(*fn)(mobj_t*)) {
    assert(current_path.block_count<128);int *v=current_path.blocks[current_path.block_count++];
    v[0]=0;v[1]=x;v[2]=y;return P_BlockThingsIterator(x,y,fn);
}
#define P_BlockLinesIterator path_lines
#define P_BlockThingsIterator path_things

/* PATH_TRAVERSE */

#undef P_BlockLinesIterator
#undef P_BlockThingsIterator
static void print_path(path_record_t *r) {
    printf("%d %d %d %d %d | %d",r->completed,r->trace.x,r->trace.y,r->trace.dx,r->trace.dy,r->block_count);
    for(int i=0;i<r->block_count;i++) for(int j=0;j<3;j++) printf(" %d",r->blocks[i][j]);
    for(int pass=0;pass<2;pass++) {
        int n=pass?r->visit_count:r->raw_count;intercept_t *hits=pass?r->visited:r->raw;
        printf(" | %d",n);
        for(int i=0;i<n;i++) printf(" %d %td %d",hits[i].isaline,
            hits[i].isaline?hits[i].d.line-lines:hits[i].d.thing-things,hits[i].frac);
    }
}
static boolean path_callback(intercept_t *hit) {
    assert(current_path.visit_count<128);
    int i=current_path.visit_count++;current_path.visited[i]=*hit;return i!=path_stop;
}
static boolean call_path(fixed_t x,fixed_t y,fixed_t x2,fixed_t y2,int flags,traverser_t fn) {
    memset(&current_path,0,sizeof(current_path));
    int result=P_PathTraverse(x,y,x2,y2,flags,fn);
    current_path.completed=result;current_path.trace=trace;return result;
}

/* SLIDE_HELPERS */

static boolean slide_callback(intercept_t *hit) {
    assert(current_path.visit_count<128);
    current_path.visited[current_path.visit_count++]=*hit;return PTR_SlideTraverse(hit);
}
static boolean slide_path(fixed_t x,fixed_t y,fixed_t x2,fixed_t y2,int flags,traverser_t fn) {
    assert(fn==PTR_SlideTraverse && slide_path_count<12);
    int result=call_path(x,y,x2,y2,flags,slide_callback);
    slide_paths[slide_path_count++]=current_path;return result;
}
static boolean slide_try(mobj_t *thing,fixed_t x,fixed_t y) {
    assert(slide_attempt_count<20);nlines=nthings=0;
    int accepted=P_TryMove(thing,x,y);int *v=slide_attempts[slide_attempt_count++];
    v[0]=x;v[1]=y;v[2]=accepted;v[3]=floatok;return accepted;
}
#define P_PathTraverse slide_path
#define P_TryMove slide_try

/* SLIDE_MOVE */

#undef P_PathTraverse
#undef P_TryMove
#undef FixedDiv
#undef abs
static int path_command(const char *op,int32_t *a,int n) {
    if(!strcmp(op,"divside") && n==6) {
        divline_t l={a[2],a[3],a[4],a[5]};printf("%d\n",P_PointOnDivlineSide(a[0],a[1],&l));
    } else if(!strcmp(op,"intercept") && n==8) {
        divline_t l={a[0],a[1],a[2],a[3]},r={a[4],a[5],a[6],a[7]};
        printf("%d\n",P_InterceptVector(&l,&r));
    } else if(!strcmp(op,"path") && n==6) {
        path_stop=a[5];call_path(a[0],a[1],a[2],a[3],a[4],path_callback);print_path(&current_path);putchar('\n');
    } else if(!strcmp(op,"momentum") && n==3) {
        assert(a[0]>=0&&a[0]<thing_count);things[a[0]].momx=a[1];things[a[0]].momy=a[2];puts("momentum");
    } else if(!strcmp(op,"hit") && n==4) {
        assert(a[0]>=0&&a[0]<line_count&&a[1]>=0&&a[1]<thing_count);
        slidemo=&things[a[1]];tmxmove=a[2];tmymove=a[3];P_HitSlideLine(&lines[a[0]]);printf("%d %d\n",tmxmove,tmymove);
    } else if(!strcmp(op,"slide") && n==1) {
        assert(use_world&&effect_mode==0&&a[0]>=0&&a[0]<thing_count);
        slide_path_count=slide_attempt_count=cross_count=0;P_SlideMove(&things[a[0]]);
        print_scene();printf(" | %d %d | %d",things[a[0]].momx,things[a[0]].momy,slide_attempt_count);
        for(int i=0;i<slide_attempt_count;i++) for(int j=0;j<4;j++) printf(" %d",slide_attempts[i][j]);
        printf(" | %d",slide_path_count);
        for(int i=0;i<slide_path_count;i++) {printf(" / ");print_path(&slide_paths[i]);}
        printf(" | %d",cross_count);
        for(int i=0;i<cross_count;i++) for(int j=0;j<5;j++) printf(" %d",cross_events[i][j]);
        putchar('\n');
    } else return 0;
    return 1;
}

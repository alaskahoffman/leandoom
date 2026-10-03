"""Original P_ThingHeightClip, standalone and with real position/pickup checks."""
from motion_reference import function

GROUPS=('height_clip','height_clip_positions')

def oracle_extension(upstream):
    wrapper=r'''
static int clip_supplied,clip_floor,clip_ceiling,clip_clear,clip_checks,clip_result;
static boolean clip_position(mobj_t *thing,fixed_t x,fixed_t y) {
    assert(x==thing->x && y==thing->y);clip_checks++;
    if(clip_supplied) {tmfloorz=clip_floor;tmceilingz=clip_ceiling;return clip_result=clip_clear;}
    return clip_result=P_CheckPosition(thing,x,y);
}
#define P_CheckPosition clip_position
'''
    return wrapper+function(upstream['src/doom/p_map.c'],'boolean P_ThingHeightClip')+'\n#undef P_CheckPosition\n'

def corpus():
    isolated=[];u=65536
    for z,oldfloor in [(0,0),(0,-u),(u,0),(-u,0),(-2147483648,-2147483648),(2147483647,0)]:
        for height in (0,1,16*u,56*u,2147483647):
            for floor in (-2147483648,-64*u,-1,0,24*u,2147483647):
                for ceiling in (-2147483648,0,56*u-1,56*u,56*u+1,128*u,2147483647):
                    for clear in (0,1):
                        isolated += [f'height {z} {height} {oldfloor} {128*u} {floor} {ceiling} {clear}']
    positions=[]
    for x in (-17,-16,-15,-1,0,1,15,16,17):
        for flags in (1,3,9,17):
            for player in (0,1):
                for noclip in (0,1):
                    for z in (0,32*u):
                        positions+=['reset','grid -128 -128 2 2',
                            f'line 0 {128*u} 0 {-128*u} 0 {128*u} {24*u} {64*u} {flags}',
                            f'world 0 {128*u} {24*u} {64*u} 0',
                            f'thing {x*u} 0 {16*u} 1',f'body 0 {z} {56*u} 0 {128*u} {noclip}',
                            'place 0',f'clip 0 {player}',f'clip 0 {player}']
    # P_CheckPosition may reject before line traversal, after a committed pickup.
    for blocker in (0,1):
        for height in (16*u,56*u):
            positions+=['reset','grid -128 -128 2 2',
                f'line 0 {128*u} 0 {-128*u} 0 {128*u} 0 {32*u} 1',
                f'world 0 {128*u} 0 {32*u} 0',
                f'thing {-u} 0 {16*u} 1',f'body 0 0 {height} 0 {128*u} 4','place 0',
                'collector 0 50 2 1 1']
            if blocker:
                positions += [f'thing {-u} 0 {16*u} 1','place 1']
            i=1+blocker
            positions += [f'thing {-u} 0 {20*u} 0',f'item {i} 12 0 0 1',f'place {i}',
                          'clip 0 1','collection','clip 0 1','collection']
    # A plane rollback performs a second query; airborne Z does not necessarily
    # return to its previous height. Floor followers use equality each time.
    for z in (0,1,16*u,96*u):
        for height in (0,16*u,56*u):
            for noclip in (0,1):
                positions+=['reset','grid -128 -128 2 2',
                    f'line {-1000*u} 0 {-1000*u} {u} 0 {128*u} 0 0 0',
                    f'world 0 {128*u} 0 {128*u} 0',f'thing 0 0 {16*u} 1',
                    f'body 0 {z} {height} 0 {128*u} {noclip}','place 0']
                for floor,ceiling in ((0,48),(0,128),(24,128),(-32,128),(0,20),(0,128),(0,0),(0,128)):
                    positions += [f'world 0 {128*u} {floor*u} {ceiling*u} 0','clip 0 1']
    return dict(zip(GROUPS,(isolated,positions)))

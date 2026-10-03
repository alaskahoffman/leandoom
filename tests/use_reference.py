"""Original use trace and scrolling-wall blocks, observed without action stubs as parity."""
from pathlib import Path
from motion_reference import function

GROUPS=('use_lines','wall_scrolling')

def oracle_extension(upstream):
    fixture=(Path(__file__).parent/'reference/use_fixture.c').read_text()
    code=fixture.replace('/* USE_TRAVERSE */',function(upstream['src/doom/p_map.c'],'boolean\tPTR_UseTraverse'))
    code=code.replace('/* USE_LINES */',function(upstream['src/doom/p_map.c'],'void P_UseLines'))
    source=upstream['src/doom/p_spec.c']
    start=source.index('    numlinespecials = 0;',source.index('void P_SpawnSpecials'))
    end=source.index('//\tInit other misc stuff',start)
    spawn=source[start:end]
    start=source.index('    for (i = 0; i < numlinespecials; i++)',source.index('void P_UpdateSpecials'))
    end=source.index('//\tDO BUTTONS',start)
    tick=source[start:end]
    return code.replace('/* SCROLL_SPAWN */',spawn).replace('/* SCROLL_TICK */',tick)

def corpus():
    u=65536
    signed=lambda x:(x+2147483648)%4294967296-2147483648
    def line(x,y,x2,y2,flags=0,floor=0,ceiling=128*u):
        return f'line {x*u} {y*u} {x2*u} {y2*u} 0 {128*u} {floor} {ceiling} {flags}'
    uses=['reset','grid -256 -256 4 4',line(-1000,0,-1000,1)]
    # Specials facing both ways, closed walls, passable windows, equal-distance
    # lines with reversed cell ordering, and repeated entries across blocks.
    for args in [(32,128,32,-128,5),(64,-128,64,128,5),(-32,-128,-32,128,5),
                 (-128,32,128,32,1),(-128,64,128,64,0),(-128,-32,128,-32,5),
                 (-64,-64,64,64,5),(32,128,32,-128,5)]:uses += [line(*args)]
    uses += [f'cell {i} '+('8 7 6 5 4 3 2 1 8' if i%2 else '1 2 3 4 5 6 7 8') for i in range(16)]
    for angle in range(8192):uses += [f'use 0 0 {signed(angle<<19)}']
    for x,y in [(0,0),(1,1),(-1,-1),(32*u,32*u),(128*u,0),(-128*u,-128*u),
                (2147483647,0),(-2147483648,0)]:
        for angle in [0,1,524287,524288,0x20000000,0x40000000,0x80000000,0xc0000000,0xffffffff]:
            uses += [f'use {x} {y} {signed(angle)}']
    # Original range endpoint and one raw unit around it; ML_BLOCKING and
    # ML_TWOSIDED do not decide whether an ordinary line has a usable opening.
    for flags in (0,1,3,5,7,17,21):
        for ceiling in (0,1,56*u-1,128*u,2147483647):
            uses+=['reset','grid -128 -128 2 2',line(-1000,0,-1000,1),line(32,128,32,-128,flags,0,ceiling),line(64,128,64,-128,5)]
            uses+=[f'cell {i} 1 2' for i in range(4)]
            for x in (-u,-1,0,1,63,64,65,u,32*u,64*u):uses += [f'use {x} 0 0']
    # A special omitted from BLOCKMAP must not be found by an all-lines scan.
    uses+=['reset','grid -128 -128 2 2',line(-1000,0,-1000,1),line(32,128,32,-128,5),'use 0 0 0']
    # Opening subtraction is signed fixed_t and may wrap even when ceiling is
    # numerically above floor. Test inverted limits and the positive one-raw gap.
    for floor,ceiling in [(-2147483648,2147483647),(2147483647,-2147483648),(1,0),(0,1)]:
        uses+=['reset','grid -128 -128 2 2',line(-1000,0,-1000,1),
               f'line {32*u} {128*u} {32*u} {-128*u} {floor} {ceiling} {floor} {ceiling} 1',line(64,128,64,-128,5)]
        uses+=[f'cell {i} 1 2' for i in range(4)]+[f'use {u} 0 0']
    scroll=[]
    for offset in (-2147483648,-2147483647,-65537,-65536,-1,0,1,65535,2147418111,2147418112,2147483647):
        scroll+=['scrollreset',f'scrollside {offset}',f'scrollside {signed(-offset)}',
                 'scrollline 48 0','scrollline 1 0','scrollline 48 0','scrollline 48 1','scrollspawn']
        scroll+=['scrolltick']*4
        scroll+=['scrollspecial 0 0','scrollspecial 1 48','scrolltick',
                 'scrollspecial 2 11','scrolltick','scrollspecial 0 48','scrolltick']
    # Exactly 64 lines, duplicate sidedefs, and an empty list.
    scroll+=['scrollreset','scrollside 0','scrollspawn','scrolltick','scrollreset','scrollside 2147418112']
    scroll+=['scrollline 48 0']*64+['scrollspawn']+['scrolltick']*70
    return dict(zip(GROUPS,(uses,scroll)))

"""Original autoaim/hitscan callbacks over the existing independent C BLOCKMAP host."""
from pathlib import Path
from motion_reference import function
GROUPS=('hitscan_aim','hitscan_shots')
def oracle_extension(upstream):
    source=upstream['src/doom/p_map.c']
    fixture=(Path(__file__).parent/'reference/hitscan_fixture.c').read_text()
    callbacks=function(source,'boolean\nPTR_AimTraverse')+function(source,'boolean PTR_ShootTraverse')
    entries=function(source,'fixed_t\nP_AimLineAttack')+function(source,'void\nP_LineAttack')
    return fixture.replace('/* HIT_CALLBACKS */',callbacks).replace('/* HIT_ENTRIES */',entries).replace('/* BULLET_SLOPE */',function(upstream['src/doom/p_pspr.c'],'void P_BulletSlope'))
def corpus():
    u=65536
    signed=lambda n:(n+2147483648)%4294967296-2147483648
    def scene(flags=1,bf=0,bc=128,sky=0,shoot=1,z=0,height=56,y=0,order='0 1 2'):
        cmds=['reset','grid -256 -256 4 4',f'line {-1000*u} 0 {-1000*u} {u} 0 {128*u} 0 {128*u} 0',
              f'line {64*u} {128*u} {64*u} {-128*u} 0 {128*u} {bf*u} {bc*u} {flags}',
              f'skyline 1 {sky&1} {(sky>>1)&1}',
              f'thing 0 0 {16*u} 1',f'shootmeta 0 1 0 0 {56*u}',
              f'thing {96*u} {y*u} {16*u} 1',f'shootmeta 1 {shoot} 0 {z*u} {height*u}',
              f'thing {96*u} {y*u} {16*u} 1',f'shootmeta 2 1 1 0 {56*u}']
        # Explicit lists test duplicates and tie order; actor lists normally
        # reside only in their origin cells, but P_PathTraverse follows the data.
        cmds += [f'cell {i} 1' for i in range(16)]
        cmds += [f'link {i} {order}' for i in range(16)]
        return cmds
    aim=scene()
    for angle in range(8192):aim += [f'aim 0 {signed(angle<<19)} {1024*u}']
    shots=[]
    for flags in (0,1,3,5,17):
        for bf,bc in ((0,128),(32,128),(0,48),(32,32),(64,32),(-64,256)):
            for sky in range(4):
                shots+=scene(flags,bf,bc,sky)
                for slope in (-65536,-40960,-1,0,1,40960,65536):
                    for damage in (0,5,15):shots += [f'shoot 0 0 {2048*u} {slope} {damage}']
                aim+=scene(flags,bf,bc,sky)
                for distance in (u,64*u,96*u,1024*u,1024*u+32768):aim += [f'aim 0 0 {distance}']
    for shoot in (0,1):
        for z,height in ((-64,56),(0,56),(36,0),(64,56),(128,128)):
            for order in ('0 1 2','0 2 1'):
                aim+=scene(shoot=shoot,z=z,height=height,order=order)
                shots+=scene(shoot=shoot,z=z,height=height,order=order)
                for angle in (0,1,0x4000000,0xfc000000,0xffffffff):
                    aim += [f'aim 0 {signed(angle)} {1024*u}',f'bulletslope 0 {signed(angle)}']
                    shots += [f'shoot 0 {signed(angle)} {2048*u} 0 10']
    # Autoaim's side retries, signed midpoint division, ignored decorations,
    # exact vertical boundaries, and a line omitted from the BLOCKMAP.
    for y in (-18,-16,-8,0,8,16,18):
        aim+=scene(y=y,z=32)+['bulletslope 0 0']
    shots+=scene(flags=0)+[f'cell {i}' for i in range(16)]+[f'shoot 0 0 {2048*u} 0 10']
    return dict(zip(GROUPS,(aim,shots)))

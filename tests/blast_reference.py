"""Unchanged DOOM 1.9 sight/radius routines with bounded synthetic fixtures."""
from pathlib import Path
from motion_reference import function

GROUPS=('sight_side','sight_portals','radius_falloff','radius_blocks')

def oracle_source(upstream):
    sight=upstream['src/doom/p_sight.c']
    fixed=upstream['src/m_fixed.c']
    code=fixed[fixed.index('fixed_t\nFixedMul'):]
    for sig in ('int\nP_DivlineSide','fixed_t\nP_InterceptVector2','boolean P_CrossSubsector','boolean P_CrossBSPNode','boolean\nP_CheckSight'):
        code+=function(sight,sig)
    code+=function(upstream['src/doom/p_maputl.c'],'boolean\nP_BlockThingsIterator')
    code+='\n#define P_CheckSight radius_sight\n'
    for sig in ('boolean PIT_RadiusAttack','void\nP_RadiusAttack'):
        code+=function(upstream['src/doom/p_map.c'],sig)
    code+='\n#undef P_CheckSight\n'
    return (Path(__file__).parent/'reference/blast_fixture.c').read_text().replace('/* ROUTINES */',code)

def corpus():
    U=65536
    side=[]
    for dx,dy in [(0,0),(0,U),(0,-U),(U,0),(-U,0),(U,U),(-U,U),(1,1),(2147483647,-2147483647)]:
        for x in [-2147483647,-U,-1,0,1,U,2147483647]:
            for y in [-U,-1,0,1,U]:
                for ox,oy in [(0,0),(U,-U),(1,1)]:
                    side.append(f'side {x} {y} {ox} {oy} {dx} {dy}')
    portals=[]
    for axis in (0,1):
        for start,end in [((0,0),(128,0)),((64,0),(128,0)),((128,0),(0,0)),((0,0),(0,128)),((64,64),(0,128)),((64,64),(128,64))]:
            for az,ah,bz,bh in [(0,56,0,10),(0,56,0,56),(0,14,64,56),(64,56,0,10),(-32,1,0,0)]:
                for ff,fc,bf,bc in [(0,128,0,128),(0,128,0,0),(0,128,24,128),(0,128,0,32),(0,128,40,48),(-32,0,-32,128)]:
                    for flags in (0,4):
                        for reject in (0,2):
                            portals.append('portal '+' '.join(map(str,[*start,az,ah,*end,bz,bh,ff,fc,bf,bc,flags,reject,axis])))
    falloff=[]
    for radius in [0,10*U,20*U,32*U]:
        for x in [0,1,10*U,127*U,128*U-1,128*U,148*U-1,148*U,160*U]:
            for y in [0,x,-x]:
                for kind in [3001,2035,7,16]:
                    for flags in (0,4):
                        for visible in (0,1):
                            falloff.append(f'falloff 0 0 {x} {y} {radius} {flags} {kind} 128 {visible}')
    blocks=[]
    for ox,oy in [(0,0),(-256*U,-256*U),(U,-U)]:
        for x in [-128*U,0,64*U,128*U,256*U,512*U,700*U]:
            for y in [0,64*U,256*U,512*U]:
                for damage in (1,64,128,256):
                    blocks.append(f'blast {ox} {oy} {x} {y} {damage}')
    return dict(zip(GROUPS,(side,portals,falloff,blocks)))

"""Non-crushing sector changes with unchanged original C callbacks and lists."""
from pathlib import Path
import re
from motion_reference import function

GROUPS=('sector_bounds','sector_changes','actor_flags')

def oracle_extension(upstream):
    setup=upstream['src/doom/p_setup.c']
    bounds=setup[setup.index('// adjust bounding box to map blocks'):]
    bounds=bounds[:bounds.index('sector->blockbox[BOXLEFT]=block;')+len('sector->blockbox[BOXLEFT]=block;')]
    flags=''
    for name,value in re.findall(r'\b(MF_\w+)\s*=\s*(0x[0-9a-fA-F]+|\d+)',upstream['src/doom/p_mobj.h']):
        flags+=f'\n#ifndef {name}\n#define {name} {value}\n#endif\n'
    entries=[]
    for entry in re.findall(r'\{\s*// MT_\w+(.*?)\n    \}',upstream['src/doom/info.c'],re.S):
        fields={key:value.strip() for value,key in re.findall(r'^\s*([^\n,]+),?\s*// (\w+)',entry,re.M)}
        if int(fields['doomednum'])>=0:
            entries.append('{'+','.join(fields[k] for k in ('doomednum','spawnhealth','flags'))+'}')
    flags+='static const int actor_meta[][3]={'+','.join(entries)+'};\n'
    fixture=(Path(__file__).parent/'reference/sector_fixture.c').read_text()
    code=fixture.replace('/* FLAGS */',flags).replace('/* BOUNDS */',bounds)
    code=code.replace('/* PIT */',function(upstream['src/doom/p_map.c'],'boolean PIT_ChangeSector'))
    return code.replace('/* CHANGE */',function(upstream['src/doom/p_map.c'],'boolean\nP_ChangeSector'))

def corpus():
    u=65536
    bounds=[]
    edges=(-2147483648,-2147483647,-128*u,-32*u-1,-32*u,0,32*u,128*u,2147483647)
    for origin in (-32768,-128,0,128,32767):
        for left in edges:
            for right in edges:
                for w,h in ((1,1),(4,3),(8,8)):
                    bounds += [f'bounds {right} {left} {left} {right} {origin} {-origin} {w} {h}']
    changes=[]
    def setup(ceiling=16*u):
        return ['reset','grid -128 -128 3 3',f'line {-1000*u} 0 {-1000*u} {u} 0 {128*u} 0 0 0',
                f'world 0 {ceiling} 0 {ceiling} 0']
    def actor(i,x,y,health=1000,shoot=0,drop=0,solid=0,height=56*u,z=0):
        return [f'thing {x*u} {y*u} {16*u} {solid}',f'body {i} {z} {height} 0 {128*u} 0',
                f'sectoractor {i} {health} {int(shoot)} {int(drop)}',f'place {i}']
    for ceiling in (-u,0,16*u,56*u-1,56*u,128*u):
        for health in (-1,0,1,1000):
            for shoot in (0,1):
                for drop in (0,1):
                    for solid in (0,1):
                        changes+=setup(ceiling)+actor(0,0,0,health,shoot,drop,solid)
                        changes+=['change 0 2 0 2 -1','change 0 2 0 2 -1']
    # Removal at head/middle/tail, death precedence, continuing after a blocker,
    # and off-grid/empty ranges. Original traversal is x-major then y-minor.
    for variant in range(8):
        changes+=setup()
        for i,(x,y) in enumerate(((-64,-64),(-64,64),(64,-64),(64,64),(192,192),(80,80),(90,90))):
            changes+=actor(i,x,y,0 if i==variant else 1000,i%2,(variant>> (i%3))&1)
        changes+=['change -2 4 -2 4 -1','change 0 1 0 1 -1','change 2 1 0 2 -1']
    # The player's height query removes an upcoming pickup: the block iterator
    # must follow its updated bnext, not the stale list captured before callback.
    for player_head in (0,1):
        for wall in (0,1):
            changes+=setup()
            changes+=actor(0,0,0,1000,0,0,height=16*u)
            changes+=['item 0 12 0 0 1']
            changes+=actor(1,0,0,50,1,0,1)+['collector 1 50 2 1 1']
            if not player_head:
                changes+=['try 0 0 0'] # relink item ahead of player
            if wall:
                changes += [f'line 0 {128*u} 0 {-128*u} 0 {128*u} 0 0 0']+[f'cell {i} 1' for i in range(9)]
            changes+=['change 0 2 0 2 1','collection','change 0 2 0 2 1','collection']
    # Rollback changes preserve gibs/removals and apply height clipping again.
    changes+=setup(128*u)
    for i in range(4): changes+=actor(i,64+i*40,0,0 if i==0 else 1000,i==2,i==1)
    for height in (16,128,0,128,-1,128):
        changes += [f'world 0 {height*u} 0 {height*u} 0','change 0 2 0 2 -1']
    metadata=[f'actormeta {i}' for i in list(range(1,90))+list(range(2001,2050))+list(range(3001,3007))+[0,9999]]
    return dict(zip(GROUPS,(bounds,changes,metadata)))

"""E1M1 floors/platforms: unchanged thinkers, selected spawn/crossing branches."""
from pathlib import Path
import re
from motion_reference import function
GROUPS=('floor_mover_steps','lift_mover_steps','e1m1_mover_spawns')

def selected_ev(source,signature,case):
    body=function(source,signature)
    # Keep original sector scan, busy check, allocation/thinker registration,
    # selected type initialization and return. Other type branches are out of scope.
    start=body.index('    secnum = -1;')
    loop=body.index('    while ((secnum',start)
    switch=body.index('\tswitch(',loop)
    selected=re.search(r'\t  case '+case+r':.*?\bbreak;',body[switch:],re.S).group()
    prologue=body[start:loop] if case=='turboLower' else '    secnum = -1;\n    rtn = 0;\n'
    ending='\n\tP_AddActivePlat(plat);' if case!='turboLower' else ''
    return prologue+body[loop:switch]+'\tswitch('+('floortype' if case=='turboLower' else 'type')+') {\n'+selected+'\n default: abort();\n }'+ending+'\n    }\n    return rtn;\n'

def oracle_source(upstream):
    header=upstream['src/doom/p_spec.h'];floor=upstream['src/doom/p_floor.c'];plat=upstream['src/doom/p_plats.c'];spec=upstream['src/doom/p_spec.c']
    types=header[header.index('typedef enum',header.index('// P_PLATS')):header.index('extern plat_t*')]
    types+=header[header.index('typedef enum',header.index('// P_FLOOR')):header.index('result_e\nT_MovePlane')]
    routines=function(spec,'sector_t*\ngetNextSector')+function(spec,'fixed_t\tP_FindLowestFloorSurrounding')+function(spec,'fixed_t\tP_FindHighestFloorSurrounding')+function(spec,'int\nP_FindSectorFromLineTag')
    routines+=function(floor,'result_e\nT_MovePlane')+function(floor,'void T_MoveFloor')+function(plat,'void T_PlatRaise')
    routines+=function(plat,'void P_AddActivePlat')+function(plat,'void P_RemoveActivePlat')
    cross=function(spec,'void\nP_CrossSpecialLine');gate=cross[cross.index('    line = &lines[linenum];'):cross.index("    // Note: could use some const's here.")]
    cases='\n'.join(re.search(r'      case '+str(n)+r':.*?\bbreak;',cross,re.S).group() for n in (36,88))
    return (Path(__file__).parent/'reference/movers_fixture.c').read_text().replace('/* TYPES */',types).replace('/* ROUTINES */',routines).replace('/* FLOOR_SPAWN */',selected_ev(floor,'int\nEV_DoFloor','turboLower')).replace('/* PLAT_SPAWN */',selected_ev(plat,'int\nEV_DoPlat','downWaitUpStay')).replace('/* CROSS_GATE */',gate).replace('/* CROSS_CASES */',cases)

def corpus():
    u=65536;floors=[];lifts=[]
    edges=[(0,-16*u),(0,0),(0,8*u),(2147483647,-2147483648),(-2147483648,2147483647)]
    for current,dest in edges:
        for speed in (0,1,u,4*u,2147483647):
            for time in (0,1,7,8,-1,-2147483648):
                for mask in range(4):floors+=[f'floor {current} {128*u} {dest} {speed} {time} {mask}']
    for status in range(4):
        for count in (-2147483648,-1,0,1,2,105):
            for wait in (-1,0,1,105):
                for current,low,high in [(0,-16*u,0),(-16*u,-16*u,0),(0,0,0),(8*u,0,4*u),(-2147483648,2147483647,2147483647)]:
                    for mask in range(4):
                        lifts += [f'lift {current} {128*u} {low} {high} {4*u} {status} {count} {wait} 0 {mask}',f'lifttick 8 {mask}']
    for mask in (0,1,2,3):
        lifts += [f'lift 0 {128*u} {-32*u} 0 {4*u} 1 0 105 0 0']
        lifts += [f'lifttick {i} {mask if i%11==0 else 0}' for i in range(1,350)]
    spawns=[]
    for special in (36,88):
        for tag in (0,7,65535):
            for player,projectile in ((1,0),(0,0),(0,1)):
                for side in (0,1):
                    for layout in range(7):
                        floor,other=[(64,0),(0,0),(0,64),(-600,-550),(-32768,32767),(32767,-32768),(64,-16)][layout]
                        spawns += ['reset',f'sector {floor} 128 {tag} {int(layout==6)}',f'sector {other} 128 {(tag+1)&65535} 0',f'sector {floor} 128 {tag} 0',
                                   f'line {0 if layout==4 else 4} 0 1 {special} {tag}','line 4 2 1 0 0']
                        if layout==3:spawns+=['line 4 0 0 0 0']
                        spawns += [f'cross 0 {player} {projectile} {side}',f'cross 0 1 0 {1-side}']
                        spawns += [f'worldtick {i}' for i in range(140)]
                        spawns += [f'cross 0 1 0 {side}']
    # No matching sector still consumes special 36; special 88 stays reusable.
    for special in (36,88):
        spawns+=['reset','sector 0 128 0 0',f'line 0 0 -1 {special} 7','cross 0 1 0 0']
    return dict(zip(GROUPS,(floors,lifts,spawns)))

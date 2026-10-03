"""Unchanged original kill/state/action routines over selected original death tables."""
import importlib.util
import re
from pathlib import Path
from motion_reference import function
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('death_data',ROOT/'scripts/generate-death.py')
data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
GROUPS=('death_kills','death_sequences','death_imp_barrel')

def oracle_source(upstream):
    rows,ids,metas,chosen=data.data()
    declarations='enum { '+','.join(f'{name}={i}' for name,i in ids.items())+' };\n'
    declarations+='enum { SPR_PLAY,SPR_POSS,SPR_SPOS,SPR_SARG,SPR_TROO,SPR_BEXP };\n'
    table='static state_t states[1000]={\n'
    for label in sorted(chosen,key=ids.get):
        spr,frame,tics,action,nxt,_=rows[ids[label]]
        table+=f'[{label}] = {{{spr},{frame},{tics},{{{action}}},{nxt},0,0}},\n'
    table+='};\nstatic info_t infos[]={\n'
    for kind,f in metas:
        table+='{'+','.join(f[k] for k in ('spawnhealth','deathstate','xdeathstate','deathsound','flags'))+'},\n'
    table+='};\n'
    enemy=upstream['src/doom/p_enemy.c'];mobj=upstream['src/doom/p_mobj.c']
    routines=''.join(function(enemy,re.search(r'void '+name+r'\s*\([^;]*?\)\s*\{',enemy).group()) for name in ('A_Scream','A_XScream','A_Fall','A_PlayerScream','A_Explode'))
    routines+='#define P_SetMobjState original_set_state\n'+function(mobj,'boolean\nP_SetMobjState')+'#undef P_SetMobjState\n'
    routines+='static boolean P_SetMobjState(mobj_t *m,int s){if(s)event(" state %d",s);return original_set_state(m,s);}\n'
    routines+=function(upstream['src/doom/p_inter.c'],'void\nP_KillMobj')
    # Exact countdown branch, with the movement and nightmare-respawn branches
    # deliberately excluded. State pointers/actions are real in this host.
    start=mobj.index('    if (mobj->tics != -1)',mobj.index('void P_MobjThinker'))
    block=mobj[start:mobj.index('    else',start)]
    routines+='static void tick(mobj_t *mobj){'+block+'}\n'
    random=upstream['src/doom/m_random.c']
    start=random.index('const unsigned char rndtable')
    table_rng=random[start:random.index('};',start)+2]+'\n'
    rng=table_rng+'static int prndindex;\n'+function(random,'int P_Random')
    return (Path(__file__).parent/'reference/death_fixture.c').read_text().replace('/* TABLES */',declarations+table).replace('/* RNG */',rng).replace('/* ROUTINES */',routines)

def corpus():
    kills=[]
    # Selected real metadata, strict gib threshold, 32-bit flags and quarter
    # height, every RNG seed. Minimal contexts here keep the corpus bounded.
    for meta,spawn,kind in [(0,100,0),(1,20,3004),(2,30,9),(3,150,3002)]:
        for health in (0,-1,-spawn,-spawn-1,-1000):
            for seed in range(256):
                flags=0x500e06
                kills.append(f'kill {meta} {kind} {flags} {health} 3670016 {0 if meta==0 else -1} 0 0 1 0 0 {seed} 0 0')
    for target in (-1,0,1,3):
        for source in (-2,-1,0,1,3):
            for net in (0,1):
                for auto in (0,1):
                    for kind in (3004,9,65,84,3006,7,16):
                        for flags,height in [(0,1),(0x7fffffff,3670017),(-1,-1),(0x400006,2147483647)]:
                            kills.append(f'kill 1 {kind} {flags} -21 {height} {target} {source} {net} {auto} 1 0 17 2147483647 2147483647')
    sequences=[]
    for meta,kind,health in [(0,0,-1),(0,0,-51),(0,0,-101),(1,3004,-1),(1,3004,-20),(1,3004,-21),(2,9,-31),(3,3002,-1000)]:
        for seed in range(8):
            for commercial in (0,1):
                sequences += [f'kill {meta} {kind} 4194310 {health} 3670016 {0 if meta==0 else -1} -1 0 0 {commercial} 0 {seed} 0 0']+['tick']*80
    extra=[]
    for meta,kind,healths,flags,height in [(4,3001,[0,-60,-61],4194310,56),(5,2035,[0,-20,-21],524294,42)]:
        for health in healths:
            for seed in range(256):
                extra += [f'kill {meta} {kind} {flags} {health} {height*65536} -1 0 0 0 0 0 {seed} 0 0']+['tick']*45
    return dict(zip(GROUPS,(kills,sequences,extra)))

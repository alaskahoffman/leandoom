"""Original single-player imp action routines; collision/sight are supplied hooks."""
from pathlib import Path
import importlib.util,re
from motion_reference import function
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('death_data',ROOT/'scripts/generate-death.py')
data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
GROUPS=('imp_actions','imp_chase','imp_sequences','imp_projectile_spawn')

def oracle_source(upstream):
    rows,ids,_,_=data.data()
    labels=[r[-1] for r in rows if r[-1].startswith(('S_TROO_','S_TBALL')) and not any(s in r[-1] for s in ('DIE','RAISE'))]
    tables='enum {SPR_TROO,SPR_BAL1};\nenum {'+','.join(f'{n}={ids[n]}' for n in labels)+'};\nstatic state_t states[1000]={\n'
    for label in labels:
        spr,frame,tics,action,nxt,_=rows[ids[label]]
        tables+=f'[{label}]={{{spr},{frame},{tics},{{{action}}},{nxt},0,0}},\n'
    tables+='};\nstatic info_t impinfo={S_TROO_STND,S_TROO_RUN1,S_TROO_ATK1,S_TROO_ATK1,sfx_bgsit1,0,sfx_bgact,8,20*FRACUNIT,sfx_popain,0,0};\nstatic info_t playerinfo={.radius=16*FRACUNIT};\n'
    fixed=upstream['src/m_fixed.c'];code=fixed[fixed.index('fixed_t\nFixedMul'):]
    table=upstream['src/tables.c'];code+=table[table.index('int SlopeDiv('):table.index('const byte gammatable')]
    main=upstream['src/doom/r_main.c'];code+=function(main,'angle_t\nR_PointToAngle\n')+function(main,'angle_t\nR_PointToAngle2')
    random=upstream['src/doom/m_random.c'];start=random.index('const unsigned char rndtable');code+=random[start:random.index('};',start)+2]+'\nstatic int prndindex;\n'
    code+=function(random,'int P_Random')+function(random,'int P_SubRandom')
    code+=function(upstream['src/doom/p_maputl.c'],'fixed_t\nP_AproxDistance')
    enemy=upstream['src/doom/p_enemy.c']
    for name in ('opposite','diags','xspeed','yspeed'):
        code+=re.search(r'(?:dirtype_t|fixed_t)\s+'+name+r'\[.*?\};',enemy,re.S).group()+'\n'
    for sig in ['boolean P_CheckMeleeRange','boolean P_CheckMissileRange','boolean P_Move','boolean P_TryWalk','void P_NewChaseDir','boolean\nP_LookForPlayers','void A_Look','void A_Chase','void A_FaceTarget','void A_TroopAttack']:
        code+=function(enemy,sig)
    projectile = r"""
#define MF_MISSILE 0x10000
#define ANGLETOFINESHIFT 19
typedef int mobjtype_t;
static info_t mobjinfo[1000]={[MT_TROOPSHOT]={.speed=10*FRACUNIT,.spawnstate=S_TBALL1,.seesound=sfx_firsht,.deathstate=S_TBALLX1,.deathsound=sfx_firxpl}};
static mobj_t bolt;
static mobj_t *P_SpawnMobj(int x,int y,int z,int type){
 (void)P_Random();bolt=(mobj_t){.x=x,.y=y,.z=z,.type=type,.flags=MF_MISSILE,.info=&mobjinfo[type],.state=&states[S_TBALL1],.tics=4};return &bolt;
}
"""
    mobj=upstream['src/doom/p_mobj.c']
    projectile+=function(mobj,'void P_ExplodeMissile')+function(mobj,'void P_CheckMissileSpawn')
    projectile+='\n#define P_SpawnMissile Original_SpawnMissile\n'+function(mobj,'mobj_t*\nP_SpawnMissile')+'\n#undef P_SpawnMissile\n'
    return (ROOT/'tests/reference/imp_fixture.c').read_text().replace('/* TABLES */',tables).replace('/* ROUTINES */',code).replace('/* PROJECTILES */',projectile)

def setup(x=128,y=0,angle=0,target=1,direction=0,mask=255,sight=1,heard=0,ambush=0,shadow=0,reaction=8,count=0,threshold=0,hit=0,attacked=0,look=0,seed=0,health=100):
    return f'setup 0 0 {x*65536} {y*65536} {angle} {target} {direction} {mask} {sight} {heard} {ambush} {shadow} {reaction} {count} {threshold} {hit} {attacked} {look} {seed} {health}'

def corpus():
    actions=[]
    for x,y in [(0,0),(59,0),(60,0),(64,0),(128,0),(1024,0),(-128,0),(64,64)]:
        for sight in (0,1):
            for reaction in (0,8):
                for hit in (0,1):
                    for seed in range(0,256,17):
                        for op in ['melee','range','enter 454']:
                            actions += [setup(x,y,sight=sight,reaction=reaction,hit=hit,seed=seed,shadow=seed%2),op]
    chase=[]
    for direction in range(9):
        for mask in [0,1,2,4,8,16,32,64,128,85,170,255]:
            for x,y in [(128,0),(128,128),(-128,128),(-128,-128),(0,0),(0,-128)]:
                for seed in (0,1,15,87,255):
                    chase += [setup(x,y,direction=direction,mask=mask,seed=seed),'newdir']
    sequences=[]
    for x in [-256,48,128,512]:
        for seed in range(8):
            for heard,ambush,sight in [(0,0,1),(1,0,0),(1,1,0),(1,1,1)]:
                sequences += [setup(x,angle=0,target=0,seed=seed,heard=heard,ambush=ambush,sight=sight,look=seed%4),'enter 442']+['tick']*120
    projectiles=[]
    for x,y in [(0,0),(1,0),(9,0),(10,0),(128,0),(-128,0),(0,128),(0,-128),(128,128),(-128,128),(128,-128),(333,71)]:
        for z in [-64,0,64]:
            for seed in range(256):
                for shadow,clear in [(0,1),(1,1),(0,0)]:
                    projectiles.append(f'spawn 0 0 0 {x*65536} {y*65536} {z*65536} {shadow} {seed} {clear}')
    return dict(zip(GROUPS,(actions,chase,sequences,projectiles)))

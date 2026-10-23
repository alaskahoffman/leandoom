"""Original player damage arithmetic/order, with explicit kill/action boundaries."""
import importlib.util
from pathlib import Path
import random
import subprocess
import tempfile
import unittest
import fidelity_reference
from motion_reference import function

ROOT=Path(__file__).resolve().parents[1]

def oracle_source():
    upstream=fidelity_reference.sources()
    spec=importlib.util.spec_from_file_location('death_data',ROOT/'scripts/generate-death.py')
    data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
    rows,ids,metas,_=data.data()
    player=next(fields for kind,fields in metas if kind=='MT_PLAYER')
    assert (player['mass'],player['painchance'],ids[player['painstate']])==('100','255',156)
    table='static state_t states[1000]={\n'
    for label in ['S_PLAY']+['S_PLAY_'+name for name in ['RUN1','RUN2','RUN3','RUN4','ATK1','ATK2','PAIN','PAIN2']]:
        _,_,tics,action,nxt,_=rows[ids[label]]
        table+=f'[{ids[label]}]={{{tics},{ids[nxt]},{int(action=="A_Pain")}}},\n'
    table+='};\n'
    fixed=upstream['src/m_fixed.c'];code=fixed[fixed.index('fixed_t\nFixedMul'):]
    trig=upstream['src/tables.c'];code+=trig[trig.index('int SlopeDiv('):trig.index('const byte gammatable')]
    main=upstream['src/doom/r_main.c']
    code+=function(main,'angle_t\nR_PointToAngle\n')+function(main,'angle_t\nR_PointToAngle2')
    rng=upstream['src/doom/m_random.c'];start=rng.index('const unsigned char rndtable')
    code+=rng[start:rng.index('};',start)+2]+'\nstatic int prndindex;\n'+function(rng,'int P_Random')
    code+=function(upstream['src/doom/p_inter.c'],'void\nP_DamageMobj')
    return (ROOT/'tests/reference/player_damage_fixture.c').read_text().replace('/* TABLES */',table).replace('/* ROUTINES */',code)

def corpus():
    # position/momentum, healths, armor, flags/powers, sector, inflictor,
    # damage/source weapon/skill/RNG, then initial animation and tics.
    base=[0,0,0,0,0,0,100,100,0,0,0,1,0,0,0,0,0,1,-128*65536,0,0,6,0,0,0,156,4]
    cases=[]
    for seed in range(256):
        for damage in [0,1,3,6,39,40,100,999,1000,10000]:
            v=base.copy();v[21]=damage;v[24]=seed;cases.append(v)
    for field,values in [(6,[-1,0,1,6,39,100]),(8,[0,1,2,3,100,200]),(9,[0,1,2]),
                         (10,[0,99,100]),(11,[0,1]),(12,[0,1]),(13,[0,1]),(14,[0,1]),
                         (15,[0,1]),(16,[0,11]),(17,[0,1]),(22,[0,1]),(23,[0,1])]:
        for value in values:
            for damage in [0,1,6,39,100,999,1000,10000]:
                v=base.copy();v[field]=value;v[21]=damage;cases.append(v)
    rng=random.Random(0x44414d47)
    for _ in range(4096):
        v=base.copy()
        for i in [0,1,2,18,19,20]:v[i]=rng.randrange(-512*65536,512*65536)
        for i in [3,4,5]:v[i]=rng.randrange(-2**31,2**31)
        v[6]=v[7]=rng.choice([1,5,20,100,200]);v[8]=rng.randrange(201);v[9]=rng.randrange(3)
        v[10]=rng.randrange(101)
        for i in [11,12,13,14,15,17,22,23]:v[i]=rng.randrange(2)
        v[16]=rng.choice([0,11]);v[21]=rng.choice([0,1,6,20,39,40,100,999,1000,10000,2**31-1])
        v[24]=rng.randrange(256);v[25]=rng.randrange(149,158);v[26]=rng.choice([1,2,4,6,12])
        if v[25]==149:v[26]=-1
        cases.append(v)
    # Strict fall-forward tests on both sides of each gate, exhausting RNG.
    for seed in range(256):
        for z in [64*65536,64*65536+1]:
            for damage in [20,21,39,40]:
                v=base.copy();v[6]=v[7]=20;v[2]=z;v[21]=damage;v[24]=seed;cases.append(v)
    return [' '.join(map(str,v)) for v in cases]

class PlayerDamageTests(unittest.TestCase):
    def test_original_player_damage_and_animation(self):
        commands=corpus()
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder);(p/'commands').write_text('\n'.join(commands)+'\n')
            (p/'oracle.c').write_text(oracle_source())
            lean=subprocess.check_output([str(ROOT/'.lake/build/bin/player-damage-probe'),str(p/'commands')])
            for opt in ['-O0','-O2']:
                subprocess.run(['cc','-std=c11','-fwrapv',opt,str(p/'oracle.c'),'-o',str(p/'oracle')],check=True,capture_output=True)
                c=subprocess.check_output([str(p/'oracle'),str(p/'commands')])
                if c!=lean:
                    for i,(a,b) in enumerate(zip(c.splitlines(),lean.splitlines())):
                        if a!=b:self.fail(f'{opt} case {i//2}: {commands[i//2]}: C {a!r}; Lean {b!r}')
                    self.fail('different output lengths')
            self.assertEqual(len(lean.splitlines()),2*len(commands))

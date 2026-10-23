"""Independent host for original effect spawning, Z motion and state transitions."""
import importlib.util
from pathlib import Path
from motion_reference import function
import fidelity_reference
ROOT=Path(__file__).resolve().parents[1]


def source():
    upstream=fidelity_reference.sources() # hashes checked by shared reference loader
    spec=importlib.util.spec_from_file_location('impact_state_data',ROOT/'scripts/generate-death.py')
    data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
    rows,ids,_,_=data.data()
    labels=[r[-1] for r in rows if r[-1].startswith(('S_PUFF','S_BLOOD')) and not r[-1].startswith('S_BLOODY')]
    tables='enum {SPR_PUFF,SPR_BLUD};\nenum {'+','.join(f'{n}={ids[n]}' for n in labels)+'};\n'
    tables+='static state_t states[1000]={\n'
    for label in labels:
        spr,frame,tics,action,nxt,_=rows[ids[label]]
        assert action=='NULL'
        tables+=f'[{label}]={{{spr},{frame},{tics},{{NULL}},{nxt}}},\n'
    tables+='};\nstatic mobjinfo_t mobjinfo[2]={{S_PUFF1,1000,8,20*FRACUNIT,16*FRACUNIT,MF_NOBLOCKMAP|MF_NOGRAVITY},{S_BLOOD1,1000,8,20*FRACUNIT,16*FRACUNIT,MF_NOBLOCKMAP}};\n'
    random=upstream['src/doom/m_random.c'];start=random.index('const unsigned char rndtable')
    routines=random[start:random.index('};',start)+2]+'\nstatic int prndindex;\n'
    routines+=function(random,'int P_Random')+function(random,'int P_SubRandom')
    mobj=upstream['src/doom/p_mobj.c']
    for signature in ['boolean\nP_SetMobjState','void P_ZMovement','void P_MobjThinker',
                      'mobj_t*\nP_SpawnMobj','void\nP_SpawnPuff','void\nP_SpawnBlood']:
        routines+=function(mobj,signature)
    return (ROOT/'tests/reference/impact_fixture.c').read_text().replace('/* TABLES */',tables).replace('/* ROUTINES */',routines)


def corpus():
    commands=[]
    # All random table starting indices, every blood-size boundary and melee
    # override. Each case follows the object through removal and beyond.
    for rng in range(256):
        for blood,damage,melee in [(0,0,0),(0,0,1),(1,8,0),(1,9,0),(1,12,0),(1,13,0)]:
            commands.append(f'{blood} {damage} {melee} {rng} 12345 -67890 2097152 0 8388608 26')
    # Floor/ceiling contacts, gravity's zero-velocity special case, signed jitter
    # and wrapping height arithmetic. Both normal and collapsed sector heights.
    for z in [-2147483648,-2147380224,-2147380225,-65536,0,65536,7*65536,120*65536,2147483647]:
        for floor,ceiling in [(0,128*65536),(0,8*65536),(-16*65536,-16*65536)]:
            for rng in [0,1,127,255]:
                for blood in [0,1]:commands.append(f'{blood} 13 0 {rng} 0 0 {z} {floor} {ceiling} 30')
    return commands

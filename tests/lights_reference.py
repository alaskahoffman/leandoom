"""Original lighting thinkers, walkover actions, topology search, and RNG order."""
from pathlib import Path
import re
from motion_reference import function
GROUPS=('light_spawns','light_sequences','light_order','light_triggers','light_trigger_sequences')
TRIGGERS=(12,13,17,35,104,79,80,81)
SPECIALS=(1,2,3,4,8,12,13,17)

def oracle_source(upstream):
    lights=upstream['src/doom/p_lights.c'];spec=upstream['src/doom/p_spec.c'];header=upstream['src/doom/p_spec.h']
    types=header[header.index('typedef struct',header.index('// P_LIGHTS')):header.index('void    P_SpawnFireFlicker')]
    rng=upstream['src/doom/m_random.c'];rng=rng[rng.index('static const unsigned char rndtable'):]
    routines=function(spec,'sector_t*\ngetNextSector')+function(spec,'int\nP_FindMinSurroundingLight')
    for sig in ('void T_FireFlicker','void P_SpawnFireFlicker','void T_LightFlash','void P_SpawnLightFlash',
                'void T_StrobeFlash','void\nP_SpawnStrobeFlash','void T_Glow','void P_SpawnGlowingLight'):
        routines+=function(lights,sig)
    routines+=function(spec,'int\nP_FindSectorFromLineTag')
    for sig in ('void EV_StartLightStrobing','void EV_TurnTagLightsOff','void\nEV_LightTurnOn'):
        routines+=function(lights,sig)
    cross=function(spec,'void\nP_CrossSpecialLine')
    # Unchanged generic nonplayer gate and lighting case blocks. The earlier
    # projectile gate is redundant for these eight player-only actions.
    gate=cross[cross.index('\n    if (!thing->player)')+1:cross.index("    // Note: could use some const's here.")]
    cases='\n'.join(re.search(r'      case '+str(n)+r':.*?\bbreak;',cross,re.S).group() for n in TRIGGERS)
    spawn=function(spec,'void P_SpawnSpecials')
    spawn=spawn[spawn.index('    sector = sectors;'):spawn.index('    //\tInit line EFFECTs')]
    fixture=(Path(__file__).parent/'reference/lights_fixture.c').read_text()
    return fixture.replace('/* TYPES_CONSTANTS */',types).replace('/* RANDOM */',rng).replace('/* ROUTINES */',routines).replace('/* SPAWN_SELECTION */',spawn).replace('/* CROSS_GATE */',gate).replace('/* CROSS_CASES */',cases)

def corpus():
    spawns=[]
    levels=(-32768,-1,0,1,8,16,64,128,255,32760,32767)
    for phase in range(256):
        for special in (*SPECIALS,0,5,9,10,14,99):
            light=levels[phase%len(levels)];other=levels[(phase*7)%len(levels)]
            spawns += [f'reset {phase} {(phase*3)&255}',f'sector {light} {special}',f'sector {other} 0',
                       f'line {4 if phase%3 else 0} 0 1','spawn']
    sequences=[]
    for special in SPECIALS:
        for light,other in [(0,0),(16,0),(128,64),(255,0),(128,128),(132,127),(127,132),(-32768,-32768),(32767,32760)]:
            sequences += [f'reset {light&255} 137',f'sector {light} {special}',f'sector {other} 0','line 4 1 0','spawn']
            sequences += ['tick']*150
            sequences += [f'set 0 {other}','tick','play 3','misc 2']+['tick']*20
    order=[]
    for phase in (0,1,17,127,254,255):
        order += [f'reset {phase} 91']
        order += [f'sector {255-i*16} {special}' for i,special in enumerate(SPECIALS)]
        # Mixed orientations, one-sided adjacency, self-references and disconnected sectors.
        order += ['line 4 0 1','line 4 2 1','line 0 2 3','line 4 3 4','line 4 4 4','line 4 5 6','line 0 7 -1','spawn']
        for i in range(512):
            if i%11==0: order += ['play 2'] # Simulate prior gameplay thinkers consuming RNG.
            if i%7==0: order += ['misc 1']
            order += ['tick']
    triggers=[]
    for special in TRIGGERS:
        for tag in (0,7,65535):
            for player in (0,1):
                for side in (0,1):
                    for layout in range(6):
                        # Neighbor order, zero-only first neighborhood, negative-only
                        # neighbors, sequential writes, specialdata and absent tags.
                        light,other=((-32768,-1) if layout==3 else (128,64))
                        triggers += ['reset 254 91',f'sector {light} 4',f'sector {other} 0','sector 224 0','sector 192 0',
                                     'line 4 0 1','line 4 2 3','line 0 0 3',
                                     f'tagsector 0 {tag if layout!=5 else (tag+1)&65535} {int(layout==4)}',
                                     f'tagsector 2 {tag if layout!=5 else (tag+1)&65535} {int(layout==4)}',
                                     f'tagsector 1 {(tag+1)&65535} 0',f'tagsector 3 {(tag+1)&65535} 0']
                        if layout==1: triggers += ['line 4 0 2']
                        if layout==2: triggers += ['set 1 0','set 0 0']
                        if layout==3: triggers += ['line 4 0 0']
                        triggers += [f'trigger 0 {special} {tag}','spawn',f'cross 0 {player} {side}',
                                     'set 0 173',f'cross 0 1 {1-side}','tick']
    trigger_sequences=[]
    # Repeated strobe creation, interleaved RNG, and existing thinkers writing
    # after instantaneous changes. Re-arm explicitly, never exceed 32 thinkers.
    for phase in range(256):
        trigger_sequences += [f'reset {phase} 71','sector 128 4','sector 64 8','sector 240 0',
                      'line 4 0 1','line 4 1 2','tagsector 0 7 0','tagsector 1 7 0','spawn']
        for special in (17,13,17,104,80,35,81,79):
            trigger_sequences += [f'trigger 0 {special} 7','cross 0 1 0','tick','play 2','misc 1','tick','tick']
        trigger_sequences += ['tick']*80
    return dict(zip(GROUPS,(spawns,sequences,order,triggers,trigger_sequences)))

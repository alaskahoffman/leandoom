"""Unchanged moving-plane and vertical-door bodies with supplied sector replies."""
from pathlib import Path
from motion_reference import function

GROUPS=('plane_steps','door_steps','door_sequences','door_runtime')

def runtime_cases():
    # Existing runtime action adapter: (special, original type, start ceiling,
    # speed, direction). Compare subsequent thinker tics to unchanged C.
    return [(1,0,-16,2,1),(31,3,-16,2,1),(118,6,-16,8,1),
            (50,2,124,2,-1),(111,5,-16,8,1),(113,7,124,8,-1)]

def runtime_commands(case):
    _,kind,ceiling,speed,direction=case
    return [f'door {kind} -1048576 {ceiling*65536} {speed*65536} 8126464 {direction} 150 0']+['tick 0']*300

def oracle_source(upstream):
    header=upstream['src/doom/p_spec.h']
    types=header[header.index('typedef enum',header.index('// P_DOORS')):header.index('#define VDOORSPEED')]
    routines=function(upstream['src/doom/p_floor.c'],'result_e\nT_MovePlane')
    routines+=function(upstream['src/doom/p_doors.c'],'void T_VerticalDoor')
    return (Path(__file__).parent/'reference/doors_fixture.c').read_text().replace('/* TYPES */',types).replace('/* ROUTINES */',routines)

def corpus():
    planes=[]
    # Exact destination, one raw unit either side, fractional steps, inverted
    # destinations, 32-bit wrap, and all callback replies including rollback.
    pairs=[(0,0),(0,1),(0,65536),(65536,0),(-65536,65536),
           (2147483647,-2147483648),(-2147483648,2147483647)]
    for floor,ceiling in pairs:
        for plane in (0,1):
            current=(floor,ceiling)[plane]
            for speed in (0,1,32768,65536,131072,524288,2147483647):
                for direction in (-1,1):
                    wrap=lambda x: (x+2147483648)%4294967296-2147483648
                    for dest in (current,wrap(current+direction*speed-1),wrap(current+direction*speed),wrap(current+direction*speed+1)):
                        for crush in (0,1):
                            for mask in range(4):
                                planes += [f'plane {floor} {ceiling} {speed} {dest} {crush} {plane} {direction} {mask}']
    doors=[]
    for kind in range(8):
        for direction in (-1,0,1,2):
            for count in (-2147483648,-1,0,1,2,150,1050,10500):
                for mask in range(4):
                    for floor,ceiling,top in [(0,0,131072),(0,131072,131072),(0,65536,131072),
                                               (0,262144,131072),(131072,65536,0)]:
                        doors += [f'door {kind} {floor} {ceiling} 131072 {top} {direction} 150 {count}',f'tick {mask}']
    sequences=[]
    for kind in range(8):
        for blocked in (False,True):
            direction=2 if kind==4 else -1 if kind in (1,2,7) else 1
            ceiling=16*65536 if direction==-1 else 0
            speed=(8 if kind>=5 else 2)*65536
            count=10500 if kind==4 else 0
            sequences += [f'door {kind} 0 {ceiling} {speed} 1048576 {direction} 150 {count}']
            for tick in range(10690 if kind==4 else 1300):
                if tick==5: sequences += [f'height 65536 {ceiling}']
                # Include obstruction on regular and past-destination attempts.
                sequences += [f'tick {3 if blocked and tick%11<3 else 0}']
    runtime=[command for case in runtime_cases() for command in runtime_commands(case)]
    return dict(zip(GROUPS,(planes,doors,sequences,runtime)))

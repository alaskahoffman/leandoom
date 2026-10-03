"""Original pickup callbacks inside real position/move/slide checks."""
from pathlib import Path
import pickup_reference

GROUPS=("pickup_contacts","pickup_movement")


def oracle_extension(upstream):
    declarations,constants,functions=pickup_reference.oracle_parts(upstream)
    return (Path(__file__).parent/'reference/contact_fixture.c').read_text().replace(
        '/* DECLARATIONS */',declarations).replace('/* CONSTANTS */',constants).replace('/* FUNCTIONS */',functions)


def corpus():
    u=65536

    def setup(health=50,flags=4,floor=0,ceiling=128*u,wall=False,enabled=1,skill=2):
        cmds=['reset','grid -128 -128 4 2',f'line {-1000*u} 0 {-1000*u} {u} 0 {128*u} 0 0 0',
              f'world 0 {128*u} {floor} {ceiling} 0',f'thing {-64*u} 0 {16*u} 1',
              f'body 0 0 {56*u} 0 {128*u} {flags}','place 0',f'physical 0 0 0 0 0 0 {41*u} 0',
              f'collector 0 {health} {skill} 1 {enabled}']
        if wall:
            cmds += [f'line 0 {128*u} 0 {-128*u} 0 {128*u} 0 0 0']+[f'cell {c} 1' for c in range(8)]
        return cmds

    def item(i,sprite=12,x=0,y=0,z=0,solid=0,dropped=0,counted=1):
        return [f'thing {x} {y} {20*u} {solid}',f'item {i} {sprite} {z} {dropped} {counted}',f'place {i}']

    contacts=[]
    for sprite in range(36):
        for wall in (False,True):
            for health in (0,50,100,200):
                for enabled in (0,1):
                    contacts+=setup(health=health,wall=wall,enabled=enabled)+item(1,sprite,dropped=1)
                    contacts+=['try 0 0 0','collection','try 0 0 0','collection']
    # Original rectangle inequalities, inclusive Z reach, no vertical solid
    # exclusion, no-clip bypass, and solidity cached before callback removal.
    for offset in (-36*u-1,-36*u,-36*u+1,0,36*u-1,36*u,36*u+1):
        for z in (-8*u-1,-8*u,-8*u+1,56*u,56*u+1):
            for flags in (4,5):
                contacts+=setup(flags=flags)+item(1,x=offset,z=z)+['try 0 0 0','collection']
    for floor,ceiling in ((24*u+1,128*u),(0,56*u-1),(0,56*u),(-64*u,128*u)):
        contacts+=setup(floor=floor,ceiling=ceiling)+item(1)+['try 0 0 0','collection']
    for solid in (0,1):
        contacts+=setup()+item(1,solid=solid)+['try 0 0 0','collection','try 0 0 0','collection']
    # Blocking actor first versus after items; removals must not skip successors.
    for blocker in (0,1,2,3):
        contacts+=setup()
        for i in range(1,5):
            if i==blocker+1:
                contacts += [f'thing 0 0 {20*u} 1',f'place {i}']
            else: contacts+=item(i,2)
        contacts+=['try 0 0 0','collection']
    for sprites in ((12,13,4),(4,13,12)):
        contacts+=setup(health=1)
        for i,sprite in enumerate(sprites,1):contacts+=item(i,sprite)
        # Head insertion reverses spawn order, with valid back links for removal.
        contacts+=['try 0 0 0','collection']
    # Items across x-major cells, and pickups whose height is measured from
    # old body Z rather than a candidate step's raised destination floor.
    contacts+=setup(floor=24*u)
    for i,x in enumerate((-20*u,20*u,129*u),1):contacts+=item(i,2,x=x,z=60*u)
    contacts+=['try 0 0 0','collection',f'try 0 {100*u} 0','collection']

    movement=[]
    for wall in (False,True):
        for mx,my in ((30*u,20*u),(-30*u,20*u),(0,0),(u,0)):
            movement+=setup(wall=wall)
            for i,(sprite,x,y) in enumerate(((2,-50,-10),(12,-30,0),(21,-10,10),(6,0,20)),1):
                movement+=item(i,sprite,x=x*u,y=y*u)
            movement+=[f'momentum 0 {mx} {my}']
            for t in range(35):
                movement += [f'worldtick 0 {25 if t<20 else 0} 0 0 {t}','collection']
    return dict(zip(GROUPS,(contacts,movement)))

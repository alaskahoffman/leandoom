"""Pinned original status number drawing, palette selection, and face state."""
from pathlib import Path
from motion_reference import function
GROUPS=('status_numbers','status_palettes','status_faces','status_widgets')

def oracle_source(upstream):
    src=upstream['src/doom/st_stuff.c']
    constants=src[src.index('// Palette indices.'):src.index('// Dimensions given in characters.')]
    funcs='\n'.join(function(src,sig) for sig in ('int ST_calcPainOffset','void ST_updateFaceWidget','void ST_doPaletteStuff'))
    funcs+='\n'+function(upstream['src/doom/st_lib.c'],'void\nSTlib_drawNum')
    widgets=function(src,'void ST_updateWidgets')
    widgets=widgets[widgets.index('{')+1:widgets.index('    // refresh everything if this is him coming back to life')]
    fixture=(Path(__file__).parent/'reference/status_fixture.c').read_text()
    return fixture.replace('/* CONSTANTS */',constants).replace('/* FUNCTIONS */',funcs).replace('/* WIDGET_SELECTION */',widgets)

def corpus():
    numbers=[f'num {v} {width} {w}' for width in (2,3) for w in (1,4,8,14)
             for v in list(range(-105,106))+[999,1000,1994,1995,2147483647,-2147483648]]
    palettes=[f'palette {d} {b} {strength} {suit}' for d in (0,1,7,8,9,48,49,55,56,100)
              for b in (0,1,7,8,16,17,24,25,100) for strength in (0,1,63,64,127,128,703,704,767,768,1024)
              for suit in (0,7,8,15,16,120,127,128,129,2100)]
    faces=[]
    def face(h=100,d=0,b=0,inv=0,weapons=3,attack=0,god=0,angle=0,bad=-1,r=0,n=1):
        faces.extend([f'face {h} {d} {b} {inv} {weapons} {attack} {god} {angle} {bad} {r}']*n)
    # Natural timers, firing hold/release, death, static persistence at ST_Start.
    for h in (200,100,81,80,61,60,41,40,21,20,1):
        face(h=h,r=h,n=36)
    face(attack=1,n=75);face(n=20)
    face(b=6,weapons=7);face(attack=1,n=75)
    face(inv=100,n=3);face(d=10,inv=100,bad=0,n=3);face(n=40)
    face(h=0,n=4);faces.append('start 3');face(n=40)
    # Ouch sign bug, priority conflicts, all direction boundaries and wraparound.
    for angle in (0,1,0x20000000,0x80000000,0xffffffff):
        for bad in (-1,0,1,0x1fffffff,0x20000000,0x20000001,0x7fffffff,0x80000000,0x80000001,0xffffffff):
            face(h=50,n=36);face(h=100,d=30,angle=angle,bad=bad);face(n=36)
            face(h=100);face(h=50,d=30,angle=angle,bad=bad);face(n=36)
    # Deterministic stateful event mixing (RNG byte supplied like ST_Ticker).
    seed=0x57face
    for _ in range(4096):
        seed=(1664525*seed+1013904223)&0xffffffff
        face(h=(seed>>8)%201,d=(seed>>24)%4,b=(seed>>20)%4,inv=int(seed%37==0),
             weapons=(seed>>11)&511,attack=seed&1,god=int(seed%71==0),angle=seed,
             bad=-1 if seed&8 else (seed*17)&0xffffffff,r=seed&255)
    widgets=[f'widgets {weapon} {keys} 17 29 43 61' for weapon in range(9) for keys in range(64)]
    return dict(zip(GROUPS,(numbers,palettes,faces,widgets)))

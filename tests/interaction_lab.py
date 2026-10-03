"""Write an original three-room test PWAD; artwork comes from the supplied IWAD.
Run: python3 tests/interaction_lab.py artifacts/interaction-lab.wad
"""
from pathlib import Path
import sys
from test_wad import pack, name, wad


def lab():
    vertices = [(-128,-96),(-128,96),(64,96),(64,-96),(80,96),(80,-96),(320,96),(320,-96)]
    # a, b, front sector, back sector, special, tag
    edges = [(0,1,0,None,0,0),(1,2,0,None,133,7),(2,3,0,1,26,0),(3,0,0,None,0,0),
             (2,4,1,None,0,0),(5,4,2,1,26,0),(5,3,1,None,0,0),
             (4,6,2,None,0,0),(6,7,2,None,0,0),(7,5,2,None,0,0)]
    lines, sides = bytearray(), bytearray()
    for i,(a,b,front,back,special,tag) in enumerate(edges):
        side_indices = []
        for sector in [front,back]:
            if sector is None:
                side_indices.append(65535)
                continue
            side_indices.append(len(sides)//30)
            middle = ('SW1BRCOM' if i == 1 else 'STARTAN3') if back is None else '-'
            sides += pack('hh',0,0) + name('BIGDOOR2' if back is not None else '-') + name('-') + name(middle) + pack('H',sector)
        lines += pack('7H',a,b,1 if back is None else 4,special,tag,*side_indices)
    segs = [(0,1,0,0),(1,2,1,0),(2,3,2,0),(3,0,3,0),
            (3,2,2,1),(2,4,4,0),(4,5,5,1),(5,3,6,0),
            (5,4,5,0),(4,6,7,0),(6,7,8,0),(7,5,9,0)]
    sectors = b''.join(pack('hh',0,ceiling)+name('FLOOR0_1')+name('CEIL3_5')+pack('hHH',224,0,tag)
                       for ceiling,tag in [(128,0),(0,7),(128,0)])
    nodes = pack('12h2H',80,96,0,-192,96,-96,64,80,96,-96,80,320,0x8001,0x8002)
    nodes += pack('12h2H',64,96,0,-192,96,-96,-128,64,96,-96,64,320,0x8000,0)
    blockmap = pack('hhHH',-128,-128,4,2) + pack('8H',*[12]*8) + pack('12H',0,*range(10),65535)
    entries = [(-80,0,0,1,7),(-16,24,0,5,7),(-16,-24,0,2001,7),(-48,64,0,2018,7),
               (224,0,180,3004,7),(240,64,0,44,7)]
    return [('E1M1',b''),('THINGS',b''.join(pack('hhHHH',*t) for t in entries)),
            ('LINEDEFS',lines),('SIDEDEFS',sides),('VERTEXES',b''.join(pack('hh',*v) for v in vertices)),
            ('SEGS',b''.join(pack('6H',a,b,0,line,side,0) for a,b,line,side in segs)),
            ('SSECTORS',pack('6H',4,0,4,4,4,8)),('NODES',nodes),('SECTORS',sectors),
            ('REJECT',b'\0\0'),('BLOCKMAP',blockmap)]


if __name__ == '__main__':
    Path(sys.argv[1]).write_bytes(wad(lab()))

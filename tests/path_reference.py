"""Pinned path/slide routines, with bounded observation-only instrumentation."""
from pathlib import Path
from motion_reference import function

GROUPS = ("path_arithmetic", "path_traversal", "slide_projection", "slide_movement")


def corpus():
    unit = 65536
    seed = 0x50415448

    def draw():
        nonlocal seed
        seed = (1664525 * seed + 1013904223) & 0xffffffff
        return seed - 0x100000000 if seed >= 0x80000000 else seed

    def line(x, y, x2, y2, flags=0, floor=0, ceiling=128*unit):
        return f"line {x*unit} {y*unit} {x2*unit} {y2*unit} 0 {128*unit} {floor} {ceiling} {flags}"

    arithmetic = []
    edges = [-2147483648,-2147483647,-8388609,-65537,-256,-1,0,1,255,65536,8388608,2147483647]
    for dx,dy in ((0,0),(0,unit),(0,-unit),(unit,0),(-unit,0),(1,1),
                  (unit,-unit),(-unit,unit),(2147483647,-2147483648)):
        arithmetic += [f"divside {x} {y} 0 0 {dx} {dy}" for x in edges for y in edges]
    arithmetic += ["divside " + " ".join(str(draw()) for _ in range(6)) for _ in range(2048)]
    # Fractions, parallel/degenerate lines, and asymmetric argument order.
    for dx,dy in ((0,0),(0,unit),(unit,0),(unit,unit),(unit,-unit),(1,255),(-257,256)):
        for dx2,dy2 in ((0,0),(0,unit),(unit,0),(-unit,unit),(unit,-unit),(255,1)):
            for x,y in ((0,0),(unit,0),(0,unit),(-1,255),(123456,-987654)):
                arithmetic += [f"intercept 0 0 {dx} {dy} {x} {y} {dx2} {dy2}"]
    arithmetic += ["intercept " + " ".join(str(draw() % (128*unit) - 64*unit) for _ in range(8))
                   for _ in range(2048)]

    traversal = ["reset", "grid -256 -256 4 4", line(-1000,-1000,-1000,-900)]
    for coords in ((0,-256,0,256),(-256,0,256,0),(-256,-256,256,256),
                   (-256,256,256,-256),(64,-256,64,256),(0,-256,0,256)):
        traversal += [line(*coords,flags=1)]
    # Unequal insertion order, duplicates within/across cells, tied lines.
    traversal += [f"cell {i} " + ("6 2 1 3 4 5 1" if i%2 else "5 3 1 6 2 4") for i in range(16)]
    for i,(x,y) in enumerate(((-160,-160),(-48,32),(16,0),(64,64),(160,160))):
        traversal += [f"thing {x*unit} {y*unit} {16*unit} {i%2}",
                      f"link {(y+256)//128*4+(x+256)//128} {i}"]
    routes = [(-240,-240,240,240),(-240,240,240,-240),(240,240,-240,-240),
              (-200,0,200,0),(0,-200,0,200),(-200,1,200,1),(1,-200,1,200),(-200,64,200,64),
              (-256,-256,-256,-256),(16,16,16,16),(-5000,5,5000,7),(0,0,0,0)]
    for route in routes:
        for flags in range(8):
            for stop in (-1,0,1):
                traversal += ["path " + " ".join(str(v*unit) for v in route) + f" {flags} {stop}"]
    for start in (-128*unit-1,-128*unit,-128*unit+1,-1,0,1):
        for length in (16*unit-1,16*unit,16*unit+1,-16*unit-1):
            traversal += [f"path {start} {7*unit} {start+length} {-7*unit} 3 -1"]
    for _ in range(1024):
        coords = [draw() % (600*unit)-300*unit for _ in range(4)]
        traversal += ["path " + " ".join(map(str,coords)) + f" {draw()%8} -1"]
    # Early-out suppresses even already-collected hits and all visitor calls.
    traversal += ["reset","grid -128 -128 2 2",line(-1000,-1000,-1000,-900),
                  line(-32,-128,-32,128,flags=1),line(0,-128,0,128)]
    traversal += [f"cell {i} 1 2" for i in range(4)]
    for end in (-unit,0,unit,64*unit):
        for flags in (1,5,7):
            traversal += [f"path {-64*unit} {unit} {end} {unit} {flags} -1"]
    # Rounding stalls in the first cell. Things are NOT deduplicated, so the
    # same two actors produce exactly 128 intercepts across 64 iterations.
    traversal += ["reset","grid -256 -256 4 4",
                  f"thing {-192*unit} {-160*unit} {16*unit} 0",
                  f"thing {-192*unit} {-160*unit} {16*unit} 1","link 0 1 0",
                  f"path {-240*unit} {-184*unit} {240*unit} {56*unit} 2 -1"]

    projection = ["reset"]
    slopes = [(0,-128,0,128),(-128,0,128,0),(-128,-128,128,128),
              (-128,128,128,-128),(-128,-37,128,37),(128,37,-128,-37)]
    projection += [line(*coords) for coords in slopes]
    projection += [f"thing {x*unit} {y*unit} {16*unit} 1" for x,y in ((-32,16),(32,-16),(0,0))]
    velocities = [(x,y) for x in (-30*unit,-unit,-1,0,1,unit,30*unit)
                       for y in (-30*unit,-unit,-1,0,1,unit,30*unit)]
    velocities += [(draw() % (60*unit)-30*unit,draw() % (60*unit)-30*unit) for _ in range(256)]
    for i in range(len(slopes)):
        for actor in range(3):
            projection += [f"hit {i} {actor} {x} {y}" for x,y in velocities]
    projection += [f"hit {i} 0 -2147483648 -2147483648" for i in (0,1)]

    slides = []

    def scene(walls, x, y, mx, my, z=0, other=None):
        commands = ["reset","grid -256 -256 4 4",line(-1000,-1000,-1000,-900)] + walls
        commands += [f"cell {i} " + " ".join(str(j+1) for j in range(len(walls))) for i in range(16)]
        commands += [f"world 0 {128*unit} 0 {128*unit} 0",
                     f"thing {x} {y} {16*unit} 1",f"body 0 {z} {56*unit} 0 {128*unit} 4","place 0"]
        if other:
            commands += [f"thing {other[0]} {other[1]} {16*unit} 1","place 1"]
        return commands + [f"momentum 0 {mx} {my}","slide 0"]

    for walls in ([line(0,128,0,-128)], [line(0,-128,0,128)],
                  [line(-128,0,128,0)], [line(128,0,-128,0)],
                  [line(0,128,0,-128),line(-128,0,128,0)],
                  [line(-128,0,128,0),line(0,128,0,-128)],
                  [line(-128,-128,128,128)], [line(-128,128,128,-128)]):
        for x,y in ((-24,-24),(-24,24),(24,-24),(24,24),(-16,-16),(-17,7)):
            for mx,my in ((30,20),(20,30),(30,30),(-30,-30),(-30,20),(30,-20),(-30,-20),(0,20),(20,0),(0,0)):
                slides += scene(walls,x*unit,y*unit,mx*unit,my*unit)
    # Height/step thresholds and the independent two-sided and blocking flags.
    for flags in (1,3,5,17):
        for floor in (0,24*unit-1,24*unit,24*unit+1):
            for ceiling in (56*unit-1,56*unit,56*unit+1,128*unit):
                slides += scene([line(0,128,0,-128,flags,floor,ceiling)],
                                -24*unit,-8*unit,30*unit,20*unit)
    # Thing-only obstruction takes Y then X fallback, retaining momentum.
    for other in ((0,0),(-24*unit,20*unit),(-24*unit,-24*unit)):
        slides += scene([], -24*unit,-24*unit,30*unit,30*unit,other=other)
    # Fine fractions around contact and the approach margin.
    for offset in (-2049,-2048,-2047,-1,0,1,2047,2048,2049):
        slides += scene([line(0,128,0,-128)],-16*unit-offset,7*unit,30*unit-1,20*unit+1)
    for z in (-1,0,1,24*unit,24*unit+1):
        slides += scene([line(0,128,0,-128,1,0,56*unit)],
                        -24*unit,-8*unit,30*unit,20*unit,z=z)
    # Cross specials during the approach and during the projected move.
    slides += scene([line(0,128,0,-128),line(-20,-128,-20,128,5),line(-128,-10,128,-10,5)],
                    -24*unit,-24*unit,30*unit,30*unit)
    for _ in range(128):
        walls = [line(-128,-37,128,37),line(0,128,0,-128)]
        coords = [draw() % (64*unit)-32*unit for _ in range(2)]
        velocities = [draw() % (60*unit)-30*unit for _ in range(2)]
        slides += scene(walls,*coords,*velocities)
    return dict(zip(GROUPS,(arithmetic,traversal,projection,slides)))


def oracle_extension(upstream):
    parts=(Path(__file__).parent / "reference/path_fixture.c").read_text()
    util=upstream["src/doom/p_maputl.c"]
    collision=upstream["src/doom/p_map.c"]
    main=upstream["src/doom/r_main.c"]
    tables=upstream["src/tables.c"]
    funcs=tables[tables.index("int SlopeDiv("):tables.index("const byte gammatable")]
    funcs += function(main,"angle_t\nR_PointToAngle\n") + function(main,"angle_t\nR_PointToAngle2")
    for sig in ("int\nP_PointOnDivlineSide","void\nP_MakeDivline","fixed_t\nP_InterceptVector",
                "boolean\nPIT_AddLineIntercepts","boolean PIT_AddThingIntercepts","boolean\nP_TraverseIntercepts"):
        funcs += function(util,sig)
    parts=parts.replace("/* PATH_FUNCTIONS */",funcs)
    parts=parts.replace("/* PATH_TRAVERSE */",function(util,"boolean\nP_PathTraverse"))
    funcs=function(util,"fixed_t\nP_AproxDistance")
    funcs+=function(collision,"void P_HitSlideLine")+function(collision,"boolean PTR_SlideTraverse")
    parts=parts.replace("/* SLIDE_HELPERS */",funcs)
    return parts.replace("/* SLIDE_MOVE */",function(collision,"void P_SlideMove"))

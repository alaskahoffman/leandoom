"""Bounded live-player position checks against unchanged pinned C routines."""
from pathlib import Path
from motion_reference import function
import path_reference
import world_reference
import contact_reference
import height_reference
import sector_reference
import use_reference
import hitscan_reference

GROUPS = ("imp_missile_collision","collision_geometry", "collision_positions", "try_move", "move_links", "move_specials") + path_reference.GROUPS + world_reference.GROUPS + contact_reference.GROUPS + height_reference.GROUPS + sector_reference.GROUPS + use_reference.GROUPS + hitscan_reference.GROUPS


def oracle_source(upstream):
    prefix, driver = (Path(__file__).parent / "reference/collision_fixture.c").read_text().split(
        "/* REFERENCE_FUNCTIONS */")
    fixed = upstream["src/m_fixed.c"]
    fixed = fixed[fixed.index("fixed_t\nFixedMul"):]
    util = upstream["src/doom/p_maputl.c"]
    code = fixed
    for signature in ("int\nP_PointOnLineSide", "int\nP_BoxOnLineSide", "void P_LineOpening",
                      "boolean\nP_BlockLinesIterator", "boolean\nP_BlockThingsIterator"):
        code += function(util, signature)
    collision = upstream["src/doom/p_map.c"]
    code += function(collision, "boolean PIT_CheckLine")
    code += function(collision, "boolean PIT_CheckThing")
    # Transparent wrappers observe callback order, without editing their bodies.
    code += r'''
static boolean traced_line(line_t *line) {
    assert(nlines<64); visited_lines[nlines++]=(int)(line-lines);
    return PIT_CheckLine(line);
}
static boolean traced_thing(mobj_t *thing) {
    assert(nthings<256); visited_things[nthings++]=(int)(thing-things);
    if(thing->flags & MF_SOLID) {
        assert(thing->x-tmx!=INT_MIN && thing->y-tmy!=INT_MIN);
    }
    return PIT_CheckThing(thing);
}
#define PIT_CheckLine traced_line
#define PIT_CheckThing traced_thing
'''
    code += function(collision, "boolean\nP_CheckPosition")
    code += "\n#undef PIT_CheckLine\n#undef PIT_CheckThing\n"
    code += function(util, "void P_UnsetThingPosition")
    code += function(util, "void\nP_SetThingPosition")
    code += r'''
static boolean checked_position(mobj_t *thing,fixed_t x,fixed_t y) {
    checked_clear=P_CheckPosition(thing,x,y);checked_count=numspechit;return checked_clear;
}
#define P_CheckPosition checked_position
'''
    code += function(collision, "boolean\nP_TryMove")
    code += "\n#undef P_CheckPosition\n"
    return prefix + code + path_reference.oracle_extension(upstream) + world_reference.oracle_extension(upstream) + contact_reference.oracle_extension(upstream) + height_reference.oracle_extension(upstream) + sector_reference.oracle_extension(upstream) + use_reference.oracle_extension(upstream) + hitscan_reference.oracle_extension(upstream) + driver


def corpus():
    unit = 65536
    seed = 0x424c4f43

    def draw():
        nonlocal seed
        seed = (1664525 * seed + 1013904223) & 0xffffffff
        return seed - 0x100000000 if seed >= 0x80000000 else seed

    def line(x, y, x2, y2, ff=0, fc=128, bf=0, bc=128, flags=1):
        return "line " + " ".join(str(v*unit) for v in (x,y,x2,y2,ff,fc,bf,bc)) + f" {flags}"

    geometry = ["reset"]
    lines = [(0,0,0,128), (0,128,0,0), (0,0,128,0), (128,0,0,0),
             (0,0,128,128), (128,128,0,0), (0,128,128,0), (128,0,0,128),
             (10,-20,10,-20), (-7,11,29,-3)]
    geometry += [line(*coords) for coords in lines]
    edges = [-2147483648, -2147483647, -8388609, -8388608, -8388607,
             -65536, -1, 0, 1, 65536, 8388607, 8388608, 8388609, 2147483647]
    for i in range(len(lines)):
        geometry += [f"point {i} {x} {y}" for x in edges for y in edges]
        for x in (-unit, -1, 0, 1, unit, 128*unit):
            for y in (-unit, -1, 0, 1, unit, 128*unit):
                for r in (0, 1, 16*unit):
                    geometry.append(f"box {i} {y+r} {y-r} {x-r} {x+r}")
    for _ in range(2048):
        geometry += [f"point {(draw() >> 8) % len(lines)} {draw()} {draw()}",
                     f"box {(draw() >> 8) % len(lines)} " + " ".join(str(draw()) for _ in range(4))]
    geometry += [f"coord {a} {b}" for a in edges for b in edges]

    positions = []
    for variant in range(16):
        positions += ["reset", "grid -128 -128 3 3", line(-1000,-1000,-1000,-900,flags=0)]
        positions += [line(0,-128,0,256,flags=variant),
                      line(-128,0,256,0,bf=24,bc=100,flags=5),
                      line(128,-128,128,256,bf=-32,bc=80,flags=5),
                      line(-128,128,256,128,bf=32,bc=80,flags=5),
                      line(-64,-64,192,192,bf=8,bc=96,flags=5)]
        # Unsorted lists, repeated entries and lines shared between cells.
        for cell in range(9):
            order = ([5,4,3,2,1,0,5] if cell % 2 else [1,2,3,4,5,1])
            positions += [f"cell {cell} " + " ".join(map(str,order))]
        if variant & 1:
            for x,y,r,solid in [(120,120,16,1),(129,120,32,1),(120,129,8,1),
                                (129,129,16,0),(-1,-1,16,1)]:
                positions += [f"thing {x*unit} {y*unit} {r*unit} {solid}"]
            positions += ["link 4 0", "link 5 1", "link 7 2", "link 8 3", "link 0 4"]
        for x in (-160,-128,-16,-1,0,1,16,112,120,127,128,129,144,255,272):
            for y in (-160,-128,-16,-1,0,1,16,112,120,127,128,129,144,255,272):
                positions.append(f"query {x*unit} {y*unit} {16*unit} 0 {128*unit} -1 0")
        positions += [f"query 0 0 {16*unit} 0 {128*unit} -1 1"]
        if variant & 1:
            positions += [f"query {-unit} {-unit} {16*unit} 0 {128*unit} 4 0"]
    # Leading zero participates even when the payload lists are empty.
    positions += ["reset", "grid -128 -128 2 2", line(0,-128,0,128,flags=0),
                  f"query 0 0 {16*unit} 0 {128*unit} -1 0"]
    # Within-cell bnext order, thing-before-wall early exit, self, exact AABB tangency.
    for order in ([0,1,2],[2,1,0]):
        positions += ["reset", "grid -128 -128 2 2", line(0,-128,0,128,flags=0)]
        positions += [f"thing 0 0 {16*unit} 0", f"thing 0 0 {16*unit} 1", f"thing 0 0 {16*unit} 1",
                      "link 3 " + " ".join(map(str,order))]
        for x,y in [(0,0),(32*unit-1,0),(32*unit,0),(32*unit+1,0),(31*unit,31*unit)]:
            positions += [f"query {x} {y} {16*unit} 0 {128*unit} -1 0"]
    # Wrapped grid endpoints and negative coordinates; no abs overflow actors.
    positions += ["reset", "grid -128 -128 2 2", line(-1000,-1000,-1000,-900,flags=0)]
    for _ in range(2048):
        positions += [f"query {draw()} {draw()} {16*unit} 0 {128*unit} -1 0"]
    # Separate cell payloads expose x-major/y-minor traversal and equal-height
    # ceiling-line ties; none of these specials is sorted geometrically.
    positions += ["reset", "grid -128 -128 2 2", line(-1000,-1000,-1000,-900,flags=0)]
    for x in (-4,-2,2,4):
        positions += [line(x,-32,x,32,bf=x,bc=80,flags=5)]
    for cell in range(4):
        positions += [f"cell {cell} {cell+1}", f"thing 0 0 {unit} 0", f"link {cell} {cell}"]
    positions += [f"query 0 0 {16*unit} 0 {128*unit} -1 0"] * 3
    groups = {"collision_geometry": geometry, "collision_positions": positions}

    def world(floor=0, ceiling=128*unit):
        return ["reset", "grid -128 -128 4 2", line(-1000,-1000,-1000,-900,flags=0),
                f"world 0 {128*unit} {floor} {ceiling} 0"]

    def actor(i,x,y,z=0,height=56*unit,flags=0,solid=1):
        return [f"thing {x} {y} {16*unit} {solid}",
                f"body {i} {z} {height} 0 {128*unit} {flags}",f"place {i}"]

    tries = []
    for floor in (-unit,-1,0,24*unit-1,24*unit,24*unit+1,64*unit):
        for z in (-unit,0,1,24*unit):
            for ceiling in (floor+56*unit-1,floor+56*unit,floor+56*unit+1,128*unit):
                for flags in (0,1,2,3,4,6,8,10):
                    tries += world(floor,ceiling) + actor(0,-64*unit,0,z=z,flags=flags)
                    tries += [f"try 0 {64*unit} 0"]
    # Dropoff differs from destination floor only when a contacted portal has a
    # lower adjacent floor. Teleport skips step-up but does NOT bypass dropoff.
    for drop in (24*unit-1,24*unit,24*unit+1,64*unit):
        for flags in (0,1,2,4,6,8,10):
            tries += world() + [f"line 0 {-128*unit} 0 {128*unit} {-drop} {128*unit} 0 {128*unit} 1"]
            tries += [f"cell {cell} 1" for cell in range(8)]
            tries += actor(0,-64*unit,0,flags=flags) + [f"try 0 {unit} 0"]
    # Walls/things fail before floatok, even if the destination has enough height.
    for wall in (False,True):
        tries += world()
        if wall:
            tries += [line(0,-128,0,128,flags=0)] + [f"cell {cell} 1" for cell in range(8)]
        else:
            tries += actor(0,0,0)
        i=0 if wall else 1
        tries += actor(i,-64*unit,0) + [f"try {i} {unit} 0"]
    # Signed differences wrap, rather than widening for the guard calculations.
    for _ in range(256):
        tries += world(draw(),draw()) + actor(0,-64*unit,0,z=draw(),height=draw(),flags=(draw()>>8)&15)
        tries += [f"try 0 {64*unit} 0"]

    links = []
    for flags in (0,1,4,16,32,48,49):
        links += world()
        for i,y in enumerate((-96,-48,0,48,96)):
            links += actor(i,-64*unit,y*unit,flags=flags,solid=0)
        # No motion still unlinks and reinserts at the head; visit middle/tail/head.
        for i in (2,0,4,2):
            links += [f"try {i} {-64*unit} {(-96+i*48)*unit}"]
        for x in (64,192,384,-129,-64):
            for i in (0,2,4):
                links += [f"try {i} {x*unit} {(-96+i*48)*unit}"]
    # Stateful solid-player traces make subsequent collision depend on relinking.
    links += world()
    for i,x in enumerate((-64,64,192)):
        links += actor(i,x*unit,0,flags=4)
    for _ in range(256):
        i=(draw()>>8)%3
        x=((draw()>>8)%448-128)*unit
        y=((draw()>>8)%192-96)*unit
        links += [f"try {i} {x} {y}"]

    specials = []
    for effect in (0,1,2):
        for flags in (0,1,2,4):
            for old,new in ((-8,8),(8,-8),(-8,-7)):
                specials += world()
                for x in (-4,0,4):
                    specials += [line(x,-64,x,64,flags=5)]
                specials += [f"cell {cell} 2 1 3" for cell in range(8)]
                specials += actor(0,old*unit,0,flags=flags)
                specials += [f"effect {effect} {old*unit} 0", f"try 0 {new*unit} 0", f"try 0 {old*unit} 0"]
    missiles = []
    # Contact equality, non-solid shootables, same-species immunity and shooter exclusion.
    for kind in (0,3001,3004,2035):
        for flags in (0,2,4,6):
            for z in (-8*unit-1,-8*unit,0,56*unit,56*unit+1):
                for x in (0,22*unit-1,22*unit):
                    for source in (-1,0,99):
                        missiles += world() + actor(0,0,0)
                        missiles += [f"missilething 0 {kind} 0 {56*unit} {flags}"]
                        sourcekind = kind if source == 0 else 3001
                        missiles += [f"missilequery {x} 0 {z} {source} {sourcekind} {roll}" for roll in (0,7,255)]
    # Missiles ignore monster/blocking flags but stop at one-sided geometry.
    for flags in (0,1,3,5,7):
        missiles += world() + [line(0,-128,0,128,flags=flags)]
        missiles += [f"cell {cell} 1" for cell in range(8)]
        missiles += [f"missilequery 0 0 {32*unit} 99 3001 0"]
    groups["imp_missile_collision"] = missiles
    groups.update(try_move=tries, move_links=links, move_specials=specials)
    groups.update(path_reference.corpus())
    groups.update(world_reference.corpus())
    groups.update(contact_reference.corpus())
    groups.update(height_reference.corpus())
    groups.update(sector_reference.corpus())
    groups.update(use_reference.corpus())
    groups.update(hitscan_reference.corpus())
    return groups

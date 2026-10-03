"""Unobstructed player physics fixtures; NOT a full player thinker or map oracle."""
from pathlib import Path

GROUPS = ("keyboard", "thrust", "move_player", "xy_movement", "motion_traces",
          "z_movement", "view_height", "physics_traces")


def function(source, signature):
    """Copy a complete original function, including its body, without substitution."""
    start = source.index(signature)
    opening = source.index("{", start)
    depth = 1
    end = opening + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end] + "\n"


def oracle_source(upstream):
    support, driver = (Path(__file__).parent / "reference/motion_fixture.c").read_text().split(
        "/* REFERENCE_FUNCTIONS */")
    game = upstream["src/doom/g_game.c"]
    # Use original movement/turn constants as well as the unchanged function.
    constants = game[game.index("fixed_t         forwardmove"):game.index("static int *weapon_keys")]
    routines = constants + function(game, "void G_BuildTiccmd")
    routines += function(upstream["src/doom/p_user.c"], "void\nP_Thrust\n")
    routines += function(upstream["src/doom/p_user.c"], "void P_MovePlayer")
    routines += function(upstream["src/doom/p_mobj.c"], "void P_XYMovement")
    routines += function(upstream["src/doom/p_mobj.c"], "void P_ZMovement")
    routines += function(upstream["src/doom/p_user.c"], "void P_CalcHeight")
    return support + routines + driver


def corpus():
    seed = 0x504c4159

    def draw():
        nonlocal seed
        seed = (1664525 * seed + 1013904223) & 0xffffffff
        return seed - 0x100000000 if seed & 0x80000000 else seed

    def body(mx=0, my=0, a=0, z=0, floor=0, frame=0, cheat=0, x=0, y=0):
        return f"body {x} {y} {mx} {my} {a} {z} {floor} {frame} {cheat}"

    # Exhaust the ten supported keyboard keys, separately at slow/fast stages.
    keys = []
    for held in (0, 4, 5, 6, 2147483647):
        for mask in range(1024):
            keys += [f"held {held}", f"key {mask} 1"]
    for dup in (1, 2, 3, 9):
        keys += ["reset"] + [f"key 4 {dup}"] * 10
        keys += [f"key 12 {dup}"] * 6 + [f"key 0 {dup}", f"key 8 {dup}"]
        keys += [f"key 72 {dup}"] * 10 + [f"key 8 {dup}"]

    thrust = ["reset"]
    for i in range(8192):
        angle = (i << 19)
        if angle >= 0x80000000:
            angle -= 0x100000000
        thrust += [body(), f"thrust {angle} 102400"]
    for _ in range(1024):
        thrust += [body(mx=draw(), my=draw()), f"thrust {draw()} {draw()}"]

    moves = ["reset"]
    for z in (-1, 0, 1):
        for f in (-128, -50, -25, -1, 0, 1, 25, 50, 127):
            for s in (-128, -40, -24, 0, 24, 40, 127):
                for a in (-32768, -1280, -320, 0, 320, 1280, 32767):
                    moves += [body(a=draw(), z=z, frame=abs(draw()) % 5), f"move {f} {s} {a}"]

    xy = ["reset"]
    edges = [-2147483648, -1966081, -1966080, -983041, -983040, -4097,
             -4096, -4095, -1, 0, 1, 4095, 4096, 4097, 983039, 983040,
             983041, 1966079, 1966080, 1966081, 2147483647]
    for mx in edges:
        for my in edges:
            for z in (-1, 0, 1):
                for active in (0, 1):
                    xy += [body(mx, my, z=z, frame=4, x=2147483647, y=-2147483648),
                           f"xy {active} 0 0"]
    for _ in range(1024):
        xy += [body(draw(), draw(), z=draw(), floor=draw(), frame=abs(draw()) % 5,
                    cheat=abs(draw()) % 2, x=draw(), y=draw()), "xy 0 0 0"]
    # Zero momentum returns before friction/frame reset, even with the cheat;
    # side commands alone inhibit stopping, but turning alone does not.
    for frame in range(5):
        for cheat in (0, 1):
            for z in (0, 1):
                for mx in (0, 1, 4095, 4096):
                    for cmd in ("xy 0 0 320", "xy 0 1 0"):
                        xy += [body(mx, z=z, frame=frame, cheat=cheat), cmd]

    traces = []
    for angle in (0, 0x40000000, -2147483648, -1073741824, 0x12345678):
        for mask in (1, 129, 161, 4, 133, 69, 201, 225):
            traces += ["reset", body(a=angle)] + [f"tick {mask} 1"] * 70 + ["tick 0 1"] * 105
    traces += ["reset"] + [f"tick {draw() & 1023} 1" for _ in range(4096)]
    groups = {"keyboard": keys, "thrust": thrust, "move_player": moves,
              "xy_movement": xy, "motion_traces": traces}

    unit = 65536
    vertical = ["reset"]
    for floor in (-64*unit, 0, 64*unit):
        for offset in (-1, 0, 1, unit, 8*unit, 72*unit, 128*unit):
            for gap in (40*unit, 56*unit, 128*unit):
                for momz in (-8*unit-1, -8*unit, -8*unit+1, -1, 0, 1, unit, 3*unit):
                    for nogravity in (0, 1):
                        vertical += [body(z=floor+offset, floor=floor),
                                     f"vertical {momz} {floor+gap} {56*unit} {nogravity}",
                                     f"view {41*unit} 0 0 0", "zmove"]
    # Raw wrapping/shift behavior is host-profile evidence, not a reachable-map claim.
    for _ in range(1024):
        vertical += [body(z=draw(), floor=draw()),
                     f"vertical {draw()} {draw()} {56*unit} {(draw() >> 8) & 1}",
                     f"view {draw()} {draw()} {draw()} {draw()}", "zmove"]

    # 409 is coprime to 8192, so this visits every bob-table index once.
    height = ["reset", body(mx=8*unit)]
    height += [f"height {time} 1 1" for time in range(8192)]
    heights = [-1, 0, 41*unit//2-1, 41*unit//2, 41*unit//2+1,
               41*unit-1, 41*unit, 41*unit+1, 2147483647, -2147483648]
    deltas = [-2147483648, -unit, -16385, -16384, -1, 0, 1, 16384, unit, 2147483647]
    for vh in heights:
        for delta in deltas:
            for ground in (0, 1):
                for live in (0, 1):
                    for cheat in (0, 1):
                        height += [body(mx=8*unit, my=-3*unit, z=20*unit, cheat=cheat),
                                   f"space 0 {40*unit}", f"view {vh} {delta} 123 456",
                                   f"height 5 {ground} {live}"]
    for _ in range(1024):
        height += [body(mx=draw(), my=draw(), z=draw(), cheat=(draw() >> 8) & 1),
                   f"space {draw()} {draw()}", f"view {draw()} {draw()} {draw()} {draw()}",
                   f"height {draw()} {(draw() >> 8) & 1} {(draw() >> 8) & 1}"]

    physics = []
    # Drops from rest/while running, landing squat recovery, then a 24-unit step.
    for drop in (1, 8, 24, 64, 128):
        for mask in (0, 129, 161):
            physics += ["reset", body(z=drop*unit), f"space 0 {(drop+128)*unit}"]
            physics += [f"physics {mask} 1 {t}" for t in range(100)]
            physics += [f"space {24*unit} {(drop+128)*unit}"]
            physics += [f"physics 0 1 {t}" for t in range(100, 160)]
    # Upward thrust and ceiling contact, with and without gravity.
    for nogravity in (0, 1):
        physics += ["reset", f"vertical {6*unit} {64*unit} {56*unit} {nogravity}"]
        physics += [f"physics 1 1 {t}" for t in range(70)]
    # At rest on the floor, the thinker skips Z even under a lowered ceiling.
    # Then a raised floor forces Z and exercises floor-before-ceiling clipping.
    physics += ["reset", f"space 0 {40*unit}", "physics 0 1 0",
                f"space {unit} {40*unit}", "physics 0 1 1", "physics 0 1 2"]
    physics += ["reset", body(z=64*unit)]
    for t in range(2048):
        if t % 128 == 0:
            physics += [f"space {((draw() >> 16) % 64)*unit} {192*unit}"]
        physics += [f"physics {(draw() >> 8) & 1023} 1 {t}"]
    groups.update(z_movement=vertical, view_height=height, physics_traces=physics)
    return groups

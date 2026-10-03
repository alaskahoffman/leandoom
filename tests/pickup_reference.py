"""Unchanged single-player pickup routines; no horizontal contact/tic oracle."""
from pathlib import Path
import re
import lighting_reference
from motion_reference import function

GROUPS = ("pickup_grants", "pickup_touch", "pickup_sequences", "pickup_metadata", "player_counters", "power_sequences", "render_colormaps")


def oracle_parts(upstream):
    source = upstream["src/doom/p_inter.c"]
    touch = function(source,"void\nP_TouchSpecialThing")
    sprites = re.findall(r"case (SPR_\w+):",touch)
    assert len(sprites)==36 and len(set(sprites))==36
    declarations = "enum {" + ",".join(sprites) + "};\n"
    declarations += "\n".join(f'#define {name} "{name}"' for name in sorted(set(re.findall(r"GOT[A-Z0-9]+",touch))))
    routines = "".join(function(source,sig) for sig in
        ("boolean\nP_GiveAmmo", "boolean\nP_GiveWeapon", "boolean\nP_GiveBody",
         "boolean\nP_GiveArmor", "void\nP_GiveCard", "boolean\nP_GivePower")) + touch
    constants = "\n".join(re.findall(r"int\s+(?:maxammo|clipammo)\[NUMAMMO\]\s*=\s*\{[^}]+\};",source))
    weapon_ammo = re.findall(r"\b(am_\w+),",upstream["src/doom/d_items.c"])
    assert len(weapon_ammo)==9
    constants += "\nstatic struct { int ammo; } weaponinfo[9]={"+",".join("{"+a+"}" for a in weapon_ammo)+"};\n"
    constants += "\n".join(re.findall(r"^#define DEH_DEFAULT_\w+[^\n]*",upstream["src/doom/deh_misc.h"],re.M))
    defaults = ("green_armor_class","blue_armor_class","max_health","max_armor","soulsphere_health","max_soulsphere","megasphere_health")
    for name in defaults:
        constants += "\n" + re.search(r"int deh_"+name+r"\s*=\s*DEH_DEFAULT_\w+;",upstream["src/doom/deh_misc.c"]).group()
    return declarations, constants, routines


def metadata_source(upstream):
    # Read the original spawn state and mobj fields, independently of Lean.
    info = upstream["src/doom/info.c"]
    states = {state: sprite for sprite, state in
              re.findall(r"\{(SPR_\w+),[^\n]+//\s*(S_\w+)", info)}
    rows = []
    for entry in re.findall(r"\{\s*// MT_\w+(.*?)\n    \}", info, re.S):
        fields = {key: value.strip() for value, key in
                  re.findall(r"^\s*([^\n,]+),?\s*// (\w+)", entry, re.M)}
        if "MF_SPECIAL" not in fields["flags"]:
            continue
        rows.append("{" + ",".join((fields["doomednum"], states[fields["spawnstate"]],
                    str(int("MF_COUNTITEM" in fields["flags"])), fields["radius"], fields["height"])) + "}")
    assert len(rows) == 36
    return "static const int pickup_metadata[36][5]={" + ",".join(rows) + "};"


def oracle_source(upstream):
    declarations, constants, routines = oracle_parts(upstream)
    fixture = (Path(__file__).parent / "reference/pickup_fixture.c").read_text()
    think = re.search(r"^#define INVERSECOLORMAP[^\n]*",upstream["src/doom/p_user.c"],re.M).group() + "\n" + function(upstream["src/doom/p_user.c"], "void P_PlayerThink")
    return fixture.replace("/* LIGHTING */",lighting_reference.oracle_extension(upstream)).replace("/* PLAYER_THINK */",think).replace("/* METADATA */", metadata_source(upstream)).replace("/* SPRITES_AND_MESSAGES */",declarations).replace("/* PICKUP_FUNCTIONS */",routines).replace("/* PICKUP_CONSTANTS */",constants)


def corpus():
    u=65536
    seed=0x5049434b

    def draw():
        nonlocal seed
        seed=(1664525*seed+1013904223)&0xffffffff
        return seed-0x100000000 if seed>=0x80000000 else seed

    def base(health=100, body=100, armor=0, typ=0, ready=1, pending=9, bonus=0, items=0, backpack=0, shadow=0):
        return f"base {health} {body} {armor} {typ} {ready} {pending} {bonus} {items} {backpack} {shadow}"

    grants=[]
    for skill in range(5):
        for ammo,capacity in enumerate((200,50,300,50)):
            for old in (0,1,capacity-1,capacity,capacity+1):
                for ready in range(9):
                    for owned in (3,511):
                        for clips in (0,1,2,5):
                            grants += ["reset",f"profile {skill} 1",base(ready=ready),f"weapons {owned}",
                                       "ammo "+" ".join(str(old if j==ammo else 0) for j in range(4)),f"giveammo {ammo} {clips}"]
    grants += ["reset","giveammo 4 1"]
    for weapon in range(9):
        for dropped in (0,1):
            for skill in (0,2,4):
                for owned in (0,3,511):
                    for ammo in ("0 0 0 0","200 50 300 50"):
                        grants += ["reset",f"profile {skill} 1",f"weapons {owned}","ammo "+ammo,
                                   f"giveweapon {weapon} {dropped}"]
    for health in (-1,0,1,24,25,74,75,89,90,99,100,101,199,200,201):
        for count in (0,1,10,25,100):
            grants += ["reset",base(health=health,body=123),f"givebody {count}"]
    for armor in (0,1,99,100,101,199,200,201):
        for typ in (0,1,2):
            for new in (1,2):
                grants += ["reset",base(armor=armor,typ=typ),f"givearmor {new}"]
    for card in range(6):
        for bonus in (0,6,100,2147483647):
            grants += ["reset",base(bonus=bonus),f"givecard {card}",f"givecard {card}"]
    for power in range(6):
        for health in (1,99,100,200):
            for existing in (0,1,9999):
                grants += ["reset",base(health=health),"powers "+" ".join([str(existing)]*6),
                           f"givepower {power}",f"givepower {power}"]
    # C -fwrapv arithmetic profile, distinct from reachable vanilla inventory.
    for _ in range(256):
        grants += ["reset",base(health=draw(),armor=draw(),typ=draw()),
                   "ammo "+" ".join(str(draw()) for _ in range(4)),f"giveammo {draw()%4} {draw()}",
                   f"givearmor {draw()}",f"givebody {draw()}"]

    touches=[]
    for sprite in range(36):
        for commercial in (0,1):
            for dropped in (0,1):
                for health in (1,75,100,200):
                    touches += ["reset",f"profile 2 {commercial}",base(health=health,body=health,bonus=31,items=7),
                                f"touch {sprite} 0 0 {56*u} {dropped} 1",
                                f"touch {sprite} 0 0 {56*u} {dropped} 1"]
    for sprite in range(36):
        for delta in (-8*u-1,-8*u,-8*u+1,56*u-1,56*u,56*u+1):
            for body in (-1,0,1):
                touches += ["reset",base(health=50,body=body),f"touch {sprite} {delta+123} 123 {56*u} 0 0"]
    # Full or above-capacity inventory, duplicate keys, and body/player health
    # disagreement expose equality guards and unconditional consumptions.
    for sprite in range(36):
        for above in (0,1,100):
            touches += ["reset",base(health=200+above,body=50,armor=200+above,typ=1,bonus=2147483647,items=2147483647),
                        f"ammo {200+above} {50+above} {300+above} {50+above}","weapons 511","cards 63",
                        "powers 9999 9999 9999 9999 9999 9999",f"touch {sprite} 0 0 {56*u} 1 1"]
    touches += ["reset",base(health=-30,body=1),f"touch 13 0 0 {56*u} 0 0"]
    # Height difference subtraction wraps before signed comparisons.
    for z,bodyz in ((-2147483648,2147483647),(2147483647,-2147483648),(0,-2147483648)):
        touches += ["reset",base(health=1),f"touch 12 {z} {bodyz} {56*u} 0 1"]

    sequences=[]
    for skill in range(5):
        sequences += ["reset",f"profile {skill} 1",base(health=1,body=1,ready=0),"ammo 0 0 0 0"]
        for sprite in (30,34,35,32,33,29,31,28,28,20,20,15,6,6,9,7,10,8,11,14,16,17,18,18,19):
            sequences += [f"touch {sprite} 0 0 {56*u} 1 1"]
        for _ in range(256):
            sequences += [f"touch {draw()%36} {(draw()%80-12)*u} 0 {56*u} {draw()%2} {draw()%2}"]
    counters=[]
    edges=[-2147483648,-2147483647,-129,-9,-8,-1,0,1,2,7,8,9,15,16,17,127,128,129,130,1050,2100,4200,2147483647]
    for power in range(6):
        for value in edges:
            for dead in (0,1):
                for shadow in (0,1):
                    counters += ["reset",base(bonus=value,shadow=shadow),f"counters {value} 99",
                        "powers "+" ".join(str(value if i==power else 0) for i in range(6)),
                        f"think {dead}","think 0"]
    # Invulnerability has priority even during its dark blink over active infrared.
    for inv in edges:
        for visor in edges:
            counters += ["reset",f"powers {inv} 1 1 1 1 {visor}","counters 1 32","think 0"]
    for _ in range(512):
        counters += ["reset",base(bonus=draw(),shadow=draw()%2),f"counters {draw()} {draw()}",
                     "powers "+" ".join(str(draw()) for _ in range(6)),"think 0"]
    power_sequences=[]
    for sprites in ((14,),(15,),(16,),(17,),(19,),(14,19),(2,6,6,9,15,16,19)):
        power_sequences += ["reset"]
        for sprite in sprites: power_sequences += [f"touch {sprite} 0 0 {56*u} 0 1"]
        for tic in range(4210):
            power_sequences += ["think 0"]
            if tic==1049: power_sequences += [f"touch {sprites[0]} 0 0 {56*u} 0 1"]
    return dict(zip(GROUPS,(grants,touches,sequences,[f"editor {kind}" for kind in range(2050)],counters,power_sequences,lighting_reference.corpus())))

"""Connected player movement: real collision, slide, friction and vertical/view order."""
from pathlib import Path
from motion_reference import function
import path_reference

GROUPS = ("world_xy", "world_physics", "walking_bridge")


def walking_cases():
    # Script masks and explicit expected tic commands test the UI adapter as
    # well as movement. Turning accelerates on the sixth held tic.
    return [
        ("forward",0,0,[(35,2,(25,0,0))]),
        ("backward",0,0,[(35,4,(-25,0,0))]),
        ("run",0,0,[(35,514,(50,0,0))]),
        ("strafe_left",0,0,[(12,8,(0,-24,0))]),
        ("strafe_right",0,0,[(12,16,(0,24,0))]),
        ("slide",47,0,[(8,18,(25,24,0))]),
        ("diagonal",0,0,[(16,530,(50,40,0))]),
        ("release",0,0,[(5,2,(25,0,0)),(70,0,(0,0,0))]),
        ("turn_left",0,0,[(5,32,(0,0,320)),(8,32,(0,0,640))]),
        ("turn_right_run",0,0,[(5,576,(0,0,-320)),(8,576,(0,0,-1280))]),
        ("opposed",0,0,[(8,30,(0,0,0))]),
    ]


def walking_commands():
    u=65536
    result=[]
    for _,x,y,segments in walking_cases():
        cmds=["reset","grid -128 -128 2 2"]
        vertices=[(-64,-64),(-64,64),(64,64),(64,-64)]
        for i,(a,b) in enumerate(vertices):
            c,d=vertices[(i+1)%4]
            cmds += [f"line {a*u} {b*u} {c*u} {d*u} {-16*u} {128*u} 0 0 2"]
        cmds += [f"cell {i} 0 1 2 3" for i in range(4)]
        cmds += [f"world {-16*u} {128*u} {-16*u} {128*u} 0",
            f"thing {x*u} {y*u} {16*u} 1",f"body 0 {-16*u} {56*u} {-16*u} {128*u} 4",
            "place 0",f"physical 0 0 0 0 0 0 {41*u} 0"]
        time=0
        for ticks,_,(f,s,a) in segments:
            for _ in range(ticks):
                cmds += [f"worldtick 0 {f} {s} {a} {time}"]
                time+=1
        result.append(cmds)
    return result


def oracle_extension(upstream):
    source = (Path(__file__).parent / "reference/world_fixture.c").read_text()
    user = upstream["src/doom/p_user.c"]
    mobj = upstream["src/doom/p_mobj.c"]
    routines = function(user, "void\nP_Thrust\n") + function(user, "void P_MovePlayer")
    routines += function(mobj, "void P_XYMovement") + function(mobj, "void P_ZMovement")
    routines += function(user, "void P_CalcHeight")
    return source.replace("/* WORLD_FUNCTIONS */", routines)


def corpus():
    u = 65536
    chunks = []
    for command in path_reference.corpus()["slide_movement"]:
        if command == "reset":
            chunks.append([])
        if not command.startswith("slide "):
            chunks[-1].append(command)
    xy = []
    for i,setup in enumerate(chunks):
        xy += setup + [f"physical 0 0 0 {i%5} 0 0 {41*u} 0", "worldxy 0 0 0 0 0"]
    # Clamp edges, positive-only splits and negative odd remainders; zero
    # momentum bypasses cheat/friction/frame reset even in the real scene.
    for mx in (-2147483648,-1966081,-1966080,-983041,-983040,-4096,-1,0,1,4095,983040,983041,1966080,2147483647):
        for my in (-1966081,-983041,-1,0,1,983041,1966081):
            for cheat in (0,1):
                xy += chunks[0] + [f"momentum 0 {mx} {my}",
                    f"physical 0 0 0 4 {cheat} 0 {41*u} 0", "worldxy 0 0 0 0 0"]
    physics = []
    for i in range(0,len(chunks),17):
        physics += chunks[i] + [f"physical 0 0 0 0 0 0 {41*u} 0"]
        for time in range(175):
            f,s,a = (50,24,0) if time<35 else ((25,-24,320) if time<70 else (0,0,0))
            physics += [f"worldtick 0 {f} {s} {a} {time}"]
    # Crossing a true sector boundary updates floor/ceiling before friction
    # and conditional Z movement; view calculation still precedes the move.
    for floor in (-64*u,-1,0,24*u-1,24*u,24*u+1):
        for ceiling in (56*u,80*u,128*u):
            physics += ["reset","grid -256 -256 4 4",
                f"line {-1000*u} 0 {-1000*u} {u} 0 {128*u} 0 0 0",
                f"line 0 {256*u} 0 {-256*u} 0 {128*u} {floor} {ceiling} 5"]
            physics += [f"cell {cell} 1" for cell in range(16)]
            physics += [f"world 0 {128*u} {floor} {ceiling} 0",f"thing {-64*u} 0 {16*u} 1",
                f"body 0 0 {56*u} 0 {128*u} 4","place 0",f"physical 0 0 0 0 0 0 {41*u} 0"]
            physics += [f"worldtick 0 {25 if t<45 else 0} 0 0 {t}" for t in range(140)]
    # Ground loss and hard landings while pressing into walls.
    for z,mz in ((64*u,0),(64*u,-8*u-1),(0,u),(0,-1)):
        physics += chunks[0] + [f"body 0 {z} {56*u} 0 {128*u} 4",
                               f"physical 0 0 {mz} 1 0 0 {41*u} 0"]
        physics += [f"worldtick 0 25 24 0 {t}" for t in range(105)]
    return dict(zip(GROUPS,(xy,physics,[c for case in walking_commands() for c in case])))

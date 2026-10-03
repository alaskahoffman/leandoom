"""Pinned C oracle and reproducible corpus. No network access unless --fetch.

Normal tests use checked-in outputs; running this script rebuilds the C oracle.
The reference function bodies are extracted verbatim from hash-checked upstream
files, never translated into a Python implementation of the same algorithms.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import urllib.request
import motion_reference
import collision_reference
import pickup_reference
import fuzz_reference
import status_reference
import lights_reference
import doors_reference
import movers_reference
import level_reference
import death_reference
import blast_reference
import imp_reference

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = Path(__file__).resolve().parent / "reference"
MANIFEST = REFERENCE / "manifest.json"
GOLDEN = REFERENCE / "expected.json.gz"
CACHE = ROOT / "artifacts/reference/chocolate-doom-3.1.1"
PROBE = ROOT / ".lake/build/bin/fidelity-probe"


def probe_for(group):
    if group in imp_reference.GROUPS:
        return ROOT / ".lake/build/bin/imp-probe"
    if group in blast_reference.GROUPS:
        return ROOT / ".lake/build/bin/blast-probe"
    if group in death_reference.GROUPS:
        return ROOT / ".lake/build/bin/death-probe"
    if group in level_reference.GROUPS:
        return ROOT / ".lake/build/bin/level-probe"
    if group in movers_reference.GROUPS:
        return ROOT / ".lake/build/bin/movers-probe"
    if group in doors_reference.GROUPS:
        return ROOT / ".lake/build/bin/doors-probe"
    if group in lights_reference.GROUPS:
        return ROOT / ".lake/build/bin/lights-probe"
    if group in status_reference.GROUPS:
        return ROOT / ".lake/build/bin/status-probe"
    if group in fuzz_reference.GROUPS:
        return ROOT / ".lake/build/bin/fuzz-probe"
    if group in pickup_reference.GROUPS:
        return ROOT / ".lake/build/bin/pickup-probe"
    if group in collision_reference.GROUPS:
        return ROOT / ".lake/build/bin/collision-probe"
    return ROOT / ".lake/build/bin/motion-probe" if group in motion_reference.GROUPS else PROBE


def digest(data):
    return hashlib.sha256(data).hexdigest()


def manifest():
    return json.loads(MANIFEST.read_text())


def sources(fetch=False):
    spec = manifest()
    result = {}
    for name, checksum in spec["files"].items():
        path = CACHE / name
        if not path.exists():
            if not fetch:
                raise RuntimeError(f"missing {path}; run scripts/test-fidelity --fetch")
            url = f"https://raw.githubusercontent.com/chocolate-doom/chocolate-doom/{spec['commit']}/{name}"
            data = urllib.request.urlopen(url, timeout=30).read()
            if digest(data) != checksum:
                raise RuntimeError(f"reference download checksum mismatch: {name}")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        data = path.read_bytes()
        if digest(data) != checksum:
            raise RuntimeError(f"reference checksum mismatch: {name}")
        result[name] = data.decode()
    return result


def corpus():
    # A specified generator avoids Python random-library/version dependencies.
    seed = 0xD0011993

    def draw():
        nonlocal seed
        seed = (1664525 * seed + 1013904223) & 0xffffffff
        return seed - 0x100000000 if seed & 0x80000000 else seed

    edges = [-2147483648, -2147483647, -1073741824, -65537, -65536,
             -65535, -32768, -2, -1, 0, 1, 2, 32767, 32768,
             65535, 65536, 65537, 1073741824, 2147483646, 2147483647]
    groups = {}
    for op in ("add", "sub", "mul"):
        pairs = [(a, b) for a in edges for b in edges]
        pairs += [(draw(), draw()) for _ in range(4096)]
        groups[op] = [f"{op} {a} {b}" for a, b in pairs]

    # Raw fixed-point nodes exercise sign shortcuts, subtraction wrapping,
    # quantized products, axes, degeneracy, and fractional partition vectors.
    sides = []
    for dx, dy in [(0, 0), (0, 65536), (0, -65536), (65536, 0),
                   (-65536, 0), (65536, 65536), (65536, -65536),
                   (-65536, 65536), (-65536, -65536), (1, 1),
                   (2147483647, -2147483648)]:
        for x in edges:
            for y in edges:
                sides.append(f"side {x} {y} 0 0 {dx} {dy}")
    sides += ["side " + " ".join(str(draw()) for _ in range(6)) for _ in range(4096)]
    groups["side"] = sides

    # Node.onLeft is the actual integration point used by the current engine.
    nodes = ["node 1 0 0 0 1 1", "node -1 0 0 0 -1 -1",
             "node 2147483647 -2147483648 -32768 32767 32767 -32768"]
    for _ in range(4096):
        x, y = draw(), draw()
        coords = [(draw() & 65535) - 32768 for _ in range(4)]
        nodes.append(f"node {x} {y} " + " ".join(map(str, coords)))
    # Bias toward sub-map-unit boundaries where exact cross products differ.
    for dx, dy in [(1, 1), (7, 11), (-13, 17), (29, -3)]:
        for k in range(-32, 33):
            for delta in (-1, 0, 1):
                nodes.append(f"node {dx*k} {dy*k+delta} 0 0 {dx} {dy}")
    groups["node"] = nodes

    groups["random"] = (["clear"] + ["play"] * 513 + ["misc"] * 513
                        + ["clear"] + ["subplay"] * 257
                        + ["clear"] + ["play", "misc", "subplay", "misc"] * 300
                        + ["clear", "play", "misc", "clear"])

    # FixedDiv inputs containing INT_MIN are outside this oracle's C domain.
    # Their explicit Lean rejection is tested separately, not labeled C parity.
    div_edges = [x for x in edges if x != -2147483648]
    pairs = [(a, b) for a in div_edges for b in div_edges]
    pairs += [(draw(), draw()) for _ in range(4096)]
    for a in div_edges + [16383, 16384, 16385, -16383, -16384, -16385]:
        boundary = abs(a) >> 14
        pairs += [(a, sign * b) for b in (boundary-1, boundary, boundary+1) for sign in (-1, 1)]
    groups["div"] = [f"div {a} {b}" for a, b in pairs if a != -2147483648 and b != -2147483648]

    groups["tables"] = ([f"sine {i}" for i in range(10240)]
                        + [f"tangent {i}" for i in range(4096)]
                        + [f"atan {i}" for i in range(2049)])

    def signed(n):
        n &= 0xffffffff
        return n - 0x100000000 if n >= 0x80000000 else n

    # Each fine-angle bin's first/last angle and the preceding angle, wrapping.
    groups["fine"] = [f"fine {signed((i << 19) + offset)}" for i in range(8192)
                      for offset in (-1, 0, (1 << 19)-1)]
    slope_edges = [0, 1, 2, 255, 256, 511, 512, 513, 65535, 65536,
                   0x1fffffff, 0x20000000, 0x7fffffff, 0x80000000, 0xffffffff]
    pairs = [(signed(a), signed(b)) for a in slope_edges for b in slope_edges]
    pairs += [(draw(), draw()) for _ in range(4096)]
    groups["slope"] = [f"slope {a} {b}" for a, b in pairs]
    # All octants, small-coordinate quantization, axes, coincident points,
    # and wrapping coordinate differences, including signed minimum values.
    angle_edges = edges + [-513, -512, -511, 511, 512, 513]
    groups["angle"] = [f"angle {x} {y} 0 0" for x in angle_edges for y in angle_edges]
    groups["angle"] += ["angle " + " ".join(str(draw()) for _ in range(4)) for _ in range(4096)]
    groups.update(motion_reference.corpus())
    groups.update(collision_reference.corpus())
    groups.update(pickup_reference.corpus())
    groups.update(fuzz_reference.corpus())
    groups.update(status_reference.corpus())
    groups.update(lights_reference.corpus())
    groups.update(doors_reference.corpus())
    groups.update(movers_reference.corpus())
    groups.update(level_reference.corpus())
    groups.update(death_reference.corpus())
    groups.update(blast_reference.corpus())
    groups.update(imp_reference.corpus())
    return groups


def input_bytes(commands):
    return ("\n".join(commands) + "\n").encode()


def run_probe(binary, commands):
    with tempfile.TemporaryDirectory(prefix="doom-fidelity-input-") as directory:
        path = Path(directory) / "input.txt"
        path.write_bytes(input_bytes(commands))
        result = subprocess.run([str(binary), str(path)], text=True, capture_output=True,
                                timeout=30, check=True)
    output = result.stdout.splitlines()
    if len(output) != len(commands):
        raise AssertionError(f"probe output count: {len(output)} != {len(commands)}")
    return output


def compare(commands, expected, actual, label):
    if len(expected) != len(commands) or len(actual) != len(commands):
        raise AssertionError(f"{label}: wrong number of results")
    for index, (want, got) in enumerate(zip(expected, actual)):
        if want != got:
            raise AssertionError(f"{label}, case {index}: {commands[index]}: expected {want}, got {got}")


def oracle_source(upstream):
    fixed = upstream["src/m_fixed.c"]
    fixed = fixed[fixed.index("fixed_t\nFixedMul"):]
    main = upstream["src/doom/r_main.c"]
    bsp = main
    bsp = bsp[bsp.index("int\nR_PointOnSide"):bsp.index("\nint\nR_PointOnSegSide")]
    angle = main[main.index("angle_t\nR_PointToAngle\n"):main.index("\nangle_t\nR_PointToAngle2")]
    tables = upstream["src/tables.c"]
    tables = tables[tables.index("int SlopeDiv("):tables.index("const byte gammatable")]
    random = upstream["src/doom/m_random.c"]
    preamble = r'''
#include <stdint.h>
#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
_Static_assert(sizeof(int) == 4, "reference requires 32-bit int");
_Static_assert(sizeof(int64_t) == 8, "reference requires 64-bit int64_t");
_Static_assert((-1 >> 1) == -1, "reference requires arithmetic right shift");
_Static_assert((int32_t)UINT32_MAX == -1, "reference requires wrapping narrowing");
typedef int fixed_t;
typedef unsigned int angle_t;
typedef struct { fixed_t x, y, dx, dy; } node_t;
#define FRACBITS 16
#define FINEANGLES 8192
#define SLOPERANGE 2048
#define ANG90 0x40000000
#define ANG180 0x80000000
#define ANG270 0xc0000000
fixed_t viewx, viewy;
'''
    driver = r'''
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    FILE *in = fopen(argv[1], "r");
    if (!in) return 2;
    char line[256], op[16];
    reset_motion();
    while (fgets(line, sizeof(line), in)) {
        if (motion_command(line)) continue;
        int32_t a=0, b=0, ox=0, oy=0, dx=0, dy=0;
        int n = sscanf(line, "%15s %" SCNd32 " %" SCNd32 " %" SCNd32
                       " %" SCNd32 " %" SCNd32 " %" SCNd32,
                       op, &a, &b, &ox, &oy, &dx, &dy);
        if (n == 3 && strcmp(op, "mul") == 0) printf("%d\n", FixedMul(a,b));
        else if (n == 3 && strcmp(op, "add") == 0) printf("%d\n", a+b);
        else if (n == 3 && strcmp(op, "sub") == 0) printf("%d\n", a-b);
        else if (n == 3 && strcmp(op, "div") == 0) {
            // Refuse the C undefined abs case, never synthesize an oracle value.
            if (a == INT_MIN || b == INT_MIN) return 4;
            printf("%d\n", FixedDiv(a,b));
        }
        else if (n == 3 && strcmp(op, "slope") == 0) printf("%d\n", SlopeDiv((unsigned)a,(unsigned)b));
        else if (n == 5 && strcmp(op, "angle") == 0) {
            viewx=ox; viewy=oy;
            printf("%u\n", R_PointToAngle(a,b));
        }
        else if (n == 2 && strcmp(op, "fine") == 0) {
            unsigned index = (unsigned)a >> 19;
            printf("%d %d\n", finesine[index], finecosine[index]);
        }
        else if (n == 2 && strcmp(op, "sine") == 0 && a >= 0 && a < 10240) printf("%d\n", finesine[a]);
        else if (n == 2 && strcmp(op, "tangent") == 0 && a >= 0 && a < 4096) printf("%d\n", finetangent[a]);
        else if (n == 2 && strcmp(op, "atan") == 0 && a >= 0 && a < 2049) printf("%u\n", tantoangle[a]);
        else if (n == 7 && (strcmp(op, "side") == 0 || strcmp(op, "node") == 0)) {
            if (strcmp(op, "node") == 0) {
                ox = (int32_t)((uint32_t)ox * 65536u);
                oy = (int32_t)((uint32_t)oy * 65536u);
                dx = (int32_t)((uint32_t)dx * 65536u);
                dy = (int32_t)((uint32_t)dy * 65536u);
            }
            node_t node = {ox,oy,dx,dy};
            printf("%d\n", R_PointOnSide(a,b,&node));
        } else if (n == 1) {
            int value;
            if (strcmp(op, "play") == 0) value = P_Random();
            else if (strcmp(op, "misc") == 0) value = M_Random();
            else if (strcmp(op, "subplay") == 0) value = P_SubRandom();
            else if (strcmp(op, "clear") == 0) { M_ClearRandom(); value = 0; }
            else return 3;
            printf("%d %d %d\n", value, prndindex, rndindex);
        } else return 3;
    }
    fclose(in);
    return 0;
}
'''
    return preamble + fixed + bsp + tables + angle + random + motion_reference.oracle_source(upstream) + driver


def reference_outputs(fetch=False):
    upstream = sources(fetch)
    groups = corpus()
    source = oracle_source(upstream)
    collision_source = collision_reference.oracle_source(upstream)
    pickup_source = pickup_reference.oracle_source(upstream)
    fuzz_source = fuzz_reference.oracle_source(upstream)
    status_source = status_reference.oracle_source(upstream)
    lights_source = lights_reference.oracle_source(upstream)
    doors_source = doors_reference.oracle_source(upstream)
    movers_source = movers_reference.oracle_source(upstream)
    level_source = level_reference.oracle_source(upstream)
    death_source = death_reference.oracle_source(upstream)
    blast_source = blast_reference.oracle_source(upstream)
    imp_source = imp_reference.oracle_source(upstream)
    compiler = shlex.split(os.environ.get("CC", "cc"))
    version = subprocess.check_output(compiler + ["--version"], text=True).splitlines()[0]
    target = subprocess.check_output(compiler + ["-dumpmachine"], text=True).strip()
    outputs = {}
    with tempfile.TemporaryDirectory(prefix="doom-c-oracle-") as directory:
        for kind, body in (("core", source), ("collision", collision_source), ("pickup", pickup_source), ("fuzz", fuzz_source), ("status", status_source), ("lights", lights_source), ("doors", doors_source), ("movers", movers_source), ("level", level_source), ("death", death_source), ("blast", blast_source), ("imp", imp_source)):
            cpath = Path(directory) / (kind + ".c")
            cpath.write_text(body)
            for opt in ("-O0", "-O2"):
                binary = Path(directory) / (kind + opt)
                subprocess.run(compiler + ["-std=c11", opt, "-fwrapv", "-Wall", "-Wextra",
                                            "-Werror", str(cpath), "-o", str(binary)], check=True)
                for name, commands in groups.items():
                    expected_kind = "imp" if name in imp_reference.GROUPS else "blast" if name in blast_reference.GROUPS else "death" if name in death_reference.GROUPS else "level" if name in level_reference.GROUPS else "movers" if name in movers_reference.GROUPS else "doors" if name in doors_reference.GROUPS else "lights" if name in lights_reference.GROUPS else "status" if name in status_reference.GROUPS else "fuzz" if name in fuzz_reference.GROUPS else "pickup" if name in pickup_reference.GROUPS else "collision" if name in collision_reference.GROUPS else "core"
                    if expected_kind != kind:
                        continue
                    output = run_probe(binary, commands)
                    if name in outputs:
                        compare(commands, outputs[name], output, f"C optimizer agreement {name}")
                    outputs[name] = output
    return {"manifest_sha256": digest(MANIFEST.read_bytes()),
            "oracle_sha256": digest((source + "\n/* collision oracle */\n" + collision_source + "\n/* pickup oracle */\n" + pickup_source + "\n/* fuzz oracle */\n" + fuzz_source + "\n/* status oracle */\n" + status_source + "\n/* lights oracle */\n" + lights_source + "\n/* doors oracle */\n" + doors_source + "\n/* movers oracle */\n" + movers_source + "\n/* level oracle */\n" + level_source + "\n/* death oracle */\n" + death_source + "\n/* blast oracle */\n" + blast_source + "\n/* imp oracle */\n" + imp_source).encode()), "compiler": version, "target": target,
            "flags": ["-std=c11", "-fwrapv", "-O0 and -O2"],
            "groups": {name: {"input_sha256": digest(input_bytes(commands)),
                              "expected": outputs[name]} for name, commands in groups.items()}}


def checked_golden():
    golden = json.loads(gzip.decompress(GOLDEN.read_bytes()))
    if golden["manifest_sha256"] != digest(MANIFEST.read_bytes()):
        raise AssertionError("reference manifest changed; regenerate/review C outputs explicitly")
    if set(golden["groups"]) != set(corpus()):
        raise AssertionError("reference corpus groups changed")
    for name, commands in corpus().items():
        if golden["groups"][name]["input_sha256"] != digest(input_bytes(commands)):
            raise AssertionError(f"corpus changed: {name}; regenerate/review C outputs explicitly")
    return golden


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true", help="download missing pinned sources")
    parser.add_argument("--record", action="store_true", help="explicitly replace golden outputs from C")
    args = parser.parse_args()
    live = reference_outputs(args.fetch)
    if args.record:
        GOLDEN.write_bytes(gzip.compress((json.dumps(live, indent=2) + "\n").encode(), compresslevel=9, mtime=0))
    golden = checked_golden()
    if live["oracle_sha256"] != golden["oracle_sha256"]:
        raise AssertionError("oracle harness changed; review and record reference outputs explicitly")
    for name, commands in corpus().items():
        expected = golden["groups"][name]["expected"]
        compare(commands, expected, live["groups"][name]["expected"], f"C/golden {name}")
        compare(commands, expected, run_probe(probe_for(name), commands), f"C/Lean {name}")
        print(f"{name}: {len(commands)} cases match C (-O0/-O2), golden outputs, and Lean")
    print(f"Reference {manifest()['commit']}; {live['compiler']}")


if __name__ == "__main__":
    main()

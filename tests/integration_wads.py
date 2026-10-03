"""Optional real-asset smoke test: python3 tests/integration_wads.py file.wad ..."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import struct
import subprocess
import sys
import tempfile

EXE = Path(__file__).resolve().parents[1] / ".lake/build/bin/lean-doom"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--simulate', action='store_true', help='advance the animated interaction simulation by 35 ticks')
    parser.add_argument('--combat', action='store_true', help='advance pistol/enemy simulation by 35 ticks')
    parser.add_argument('wads', nargs='+')
    args = parser.parse_args()
    report = []
    with tempfile.TemporaryDirectory() as directory:
        for arg in args.wads:
            path = Path(arg).resolve()
            data = path.read_bytes()
            count, offset = struct.unpack_from("<II", data, 4)
            maps = []
            for i in range(count):
                label = data[offset + 16*i + 8:offset + 16*i + 16].split(b"\0")[0].decode("ascii")
                if re.fullmatch(r"E\dM\d|MAP\d\d", label) and label not in maps:
                    maps.append(label)
            subprocess.run([str(EXE), "validate", str(path)], check=True, capture_output=True, timeout=30)
            for name in maps:
                output = Path(directory) / "frame.ppm"
                command = ["render-combat", name, "35:0"] if args.combat else ["render-sim", name, "35:0"] if args.simulate else ["render", name]
                subprocess.run([str(EXE), *command, str(output), str(path)],
                                        check=True, capture_output=True, timeout=15)
                frame = output.read_bytes()
                header, dimensions, maximum, pixels = frame.split(b"\n", 3)
                assert (header, dimensions, maximum) == (b"P6", b"320 200", b"255")
                assert len(pixels) == 192000 and any(pixels), name
                report.append({"wad": path.name, "map": name, "sha256": hashlib.sha256(frame).hexdigest()})
    print(json.dumps({"mode": "combat" if args.combat else "simulation" if args.simulate else "static", "rendered": len(report), "frames": report}, indent=2))


if __name__ == "__main__":
    main()

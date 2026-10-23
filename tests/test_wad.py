"""Black-box tests: independently encode WAD bytes and invoke the Lean executable.

No game assets or third-party Python packages are required.
"""
import copy
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/lean-doom"


def pack(fmt, *values):
    return struct.pack("<" + fmt, *values)


def name(s):
    return s.encode("ascii").ljust(8, b"\0")


def room(shift=0):
    vertices = [(-64 + shift, -64), (-64 + shift, 64),
                (64 + shift, 64), (64 + shift, -64)]
    return [
        ("E1M1", b""),
        ("THINGS", pack("hhHHH", shift, 0, 90, 1, 7)),
        ("LINEDEFS", b"".join(pack("7H", i, (i + 1) % 4, 1, 0, 0, 0, 65535)
                              for i in range(4))),
        ("SIDEDEFS", pack("hh", -8, 16) + name("-") * 2 + name("WALL") + pack("H", 0)),
        ("VERTEXES", b"".join(pack("hh", *v) for v in vertices)),
        ("SEGS", b"".join(pack("6H", i, (i + 1) % 4, [16384,0,49152,32768][i], i, 0, 0)
                          for i in range(4))),
        ("SSECTORS", pack("HH", 4, 0)),
        ("NODES", b""),
        ("SECTORS", pack("hh", -16, 128) + name("FLOOR") + name("CEIL") + pack("hHH", 160, 0, 0)),
        ("REJECT", b"\0"),
        # Cover the whole room now that walking uses the actual BLOCKMAP.
        # All four cells share an ordered conservative line list.
        ("BLOCKMAP", pack("hhHH4H6H", shift-128, -128, 2, 2, 8, 8, 8, 8, 0, 0, 1, 2, 3, 65535)),
    ]


def wad(lumps, kind=b"PWAD"):
    body = bytearray()
    directory = bytearray()
    for label, data in lumps:
        directory += pack("II", 12 + len(body), len(data)) + name(label)
        body += data
    return kind + pack("II", len(lumps), 12 + len(body)) + body + directory


class WadTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.directory = Path(self.tmp.name)
        self.lumps = room()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, data, filename="test.wad"):
        p = self.directory / filename
        p.write_bytes(data)
        return p

    def run_cli(self, *args, ok=True):
        result = subprocess.run([str(EXE), *map(str, args)], capture_output=True,
                                text=True, timeout=10)
        if ok:
            self.assertEqual(result.returncode, 0, result.stderr)
        else:
            self.assertGreater(result.returncode, 0, result.stdout + result.stderr)
        return result

    def reject(self, lumps, message):
        result = self.run_cli("validate", self.write(wad(lumps)), ok=False)
        self.assertIn(message, result.stderr)

    def replace(self, label, payload):
        return [(n, payload if n == label else b) for n, b in self.lumps]

    def test_valid_room_and_signed_coordinates(self):
        path = self.write(wad(self.lumps, b"IWAD"))
        output = self.directory / "room.svg"
        result = self.run_cli("map", "e1m1", output, path)
        self.assertIn("4 vertices, 4 linedefs", result.stdout)
        svg = ET.parse(output).getroot()
        lines = svg.findall(".//{http://www.w3.org/2000/svg}line")
        self.assertEqual(len(lines), 4)
        self.assertEqual(lines[0].attrib["x1"], "-64")
        self.assertEqual(lines[0].attrib["y1"], "64")
        self.assertEqual(lines[0].attrib["y2"], "-64")

    def test_last_map_group_wins_across_archives(self):
        base = self.write(wad(self.lumps, b"IWAD"), "base.wad")
        patch = self.write(wad(room(1000)), "patch.wad")
        output = self.directory / "patched.svg"
        self.run_cli("map", "E1M1", output, base, patch)
        line = ET.parse(output).find(".//{http://www.w3.org/2000/svg}line")
        self.assertEqual(line.attrib["x1"], "936")
        result = self.run_cli("inspect", base, patch)
        self.assertIn("Map markers (1): E1M1", result.stdout)

    def test_last_map_group_wins_inside_archive(self):
        path = self.write(wad(self.lumps + room(500)))
        output = self.directory / "patched.svg"
        self.run_cli("map", "E1M1", output, path)
        self.assertIn('x1="436"', output.read_text())

    def test_map_must_not_cross_archives(self):
        a = self.write(wad(self.lumps[:5]), "a.wad")
        b = self.write(wad(self.lumps[5:]), "b.wad")
        result = self.run_cli("validate", a, b, ok=False)
        self.assertIn("archive boundary", result.stderr)

    def test_all_truncations_fail(self):
        data = wad(self.lumps)
        for cut in range(len(data)):
            with self.subTest(cut=cut):
                self.run_cli("validate", self.write(data[:cut]), ok=False)

    def test_invalid_signature(self):
        self.run_cli("inspect", self.write(b"NOPE" + wad(self.lumps)[4:]), ok=False)

    def test_negative_header_fields(self):
        for offset in (4, 8):
            data = bytearray(wad(self.lumps))
            struct.pack_into("<I", data, offset, 0xffffffff)
            result = self.run_cli("inspect", self.write(data), ok=False)
            self.assertIn("negative WAD header field", result.stderr)

    def test_zero_length_marker_can_have_arbitrary_offset(self):
        data = bytearray(wad(self.lumps))
        directory = struct.unpack_from("<I", data, 8)[0]
        struct.pack_into("<I", data, directory, 0xffffffff)
        self.run_cli("validate", self.write(data))

    def test_lump_payload_out_of_bounds(self):
        data = bytearray(wad(self.lumps))
        directory = struct.unpack_from("<I", data, 8)[0]
        struct.pack_into("<I", data, directory + 16, len(data) + 100)
        result = self.run_cli("inspect", self.write(data), ok=False)
        self.assertIn("exceeds", result.stderr)

    def test_negative_lump_size(self):
        data = bytearray(wad(self.lumps))
        directory = struct.unpack_from("<I", data, 8)[0]
        struct.pack_into("<I", data, directory + 16 + 4, 0xffffffff)
        result = self.run_cli("inspect", self.write(data), ok=False)
        self.assertIn("negative size", result.stderr)

    def test_partial_record(self):
        self.reject(self.replace("VERTEXES", b"\0"), "record size 4")

    def test_wrong_map_lump_order(self):
        lumps = copy.copy(self.lumps)
        lumps[1], lumps[2] = lumps[2], lumps[1]
        self.reject(lumps, "expected THINGS")

    def test_incomplete_patch_does_not_fall_back(self):
        base = self.write(wad(self.lumps), "base.wad")
        patch = self.write(wad(self.lumps[:2]), "patch.wad")
        result = self.run_cli("validate", base, patch, ok=False)
        self.assertIn("incomplete map group", result.stderr)

    def test_bad_map_references(self):
        for label, offset, value, message in [
            ("LINEDEFS", 0, 400, "bad vertex"),
            ("LINEDEFS", 10, 65535, "bad front sidedef"),
            ("LINEDEFS", 12, 200, "bad back sidedef"),
            ("LINEDEFS", 4, 4, "two-sided line without back"),
            ("SIDEDEFS", 28, 20, "bad sector"),
            ("SEGS", 6, 20, "bad linedef or side"),
            ("SEGS", 8, 1, "absent sidedef"),
            ("SSECTORS", 0, 10, "bad seg range"),
        ]:
            with self.subTest(label=label, message=message):
                payload = bytearray(dict(self.lumps)[label])
                struct.pack_into("<H", payload, offset, value)
                self.reject(self.replace(label, payload), message)

    def test_bsp_children_and_cycles(self):
        prefix = pack("12h", 0, 0, 0, 128, *([0] * 8))
        for children, message in [((0, 0x8000), "BSP cycle"),
                                  ((8, 0x8000), "bad node child"),
                                  ((0x8001, 0x8000), "bad subsector child")]:
            with self.subTest(children=children):
                self.reject(self.replace("NODES", prefix + pack("2H", *children)), message)
        # A shared child is not a cycle.
        nodes = prefix + pack("2H", 0x8000, 0x8000) + prefix + pack("2H", 0, 0)
        self.run_cli("validate", self.write(wad(self.replace("NODES", nodes))))

    def test_blockmap_errors(self):
        for payload, message in [
            (pack("hhHH", 0, 0, 0, 1), "empty grid"),
            (pack("hhHHHHH", 0, 0, 1, 1, 5, 0, 0), "unterminated list"),
            (pack("hhHHHHH", 0, 0, 1, 1, 1, 0, 65535), "overlaps header"),
            (pack("hhHHHHH", 0, 0, 1, 1, 5, 1, 65535), "missing leading zero"),
            (pack("hhHHHHHH", 0, 0, 1, 1, 5, 0, 40, 65535), "bad linedef"),
        ]:
            with self.subTest(message=message):
                self.reject(self.replace("BLOCKMAP", payload), message)

    def test_hexen_format_rejected(self):
        self.reject(self.lumps + [("BEHAVIOR", b"")], "Hexen-format")

    def test_missing_map_and_invalid_cli(self):
        path = self.write(wad(self.lumps))
        self.run_cli("map", "MAP01", self.directory / "a.svg", path, ok=False)
        self.run_cli("map", "E1M1", self.directory / "a.wad", path, ok=False)
        self.run_cli("validate", ok=False)
        self.run_cli("unknown-command", ok=False)
        self.run_cli("--help")


if __name__ == "__main__":
    unittest.main(verbosity=2)

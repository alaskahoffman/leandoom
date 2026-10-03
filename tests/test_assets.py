"""Independent WAD artwork encoder and pixel-level assertions against Lean output."""
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
import math

from test_wad import EXE, name, pack, room, wad
from test_render import two_rooms


def rgb(index):
    return bytes((index, 255-index, (index*3) % 256))


def patch(rows, left=0, top=0):
    height, width = len(rows), len(rows[0])
    directory, posts = bytearray(), bytearray()
    for x in range(width):
        directory += pack("I", 8 + width*4 + len(posts))
        y = 0
        while y < height:
            if rows[y][x] is None:
                y += 1
                continue
            start = y
            colors = bytearray()
            while y < height and rows[y][x] is not None:
                colors.append(rows[y][x])
                y += 1
            posts += bytes((start, len(colors), 0)) + colors + b"\0"
        posts += b"\xff"
    return pack("HHhh", width, height, left, top) + directory + posts


def definitions(entries):
    body, offsets = bytearray(), bytearray()
    for label, width, height, placements in entries:
        offsets += pack("I", 4 + 4*len(entries) + len(body))
        body += name(label) + pack("IHHIH", 0, width, height, 0, len(placements))
        for x, y, index in placements:
            body += pack("hhHHH", x, y, index, 1, 0)
    return pack("I", len(entries)) + offsets + body


def artwork(rows=None, texture_names=("WALL",), flats=("FLOOR", "CEIL")):
    if rows is None:
        rows = [[1+x+8*y for x in range(8)] for y in range(8)]
    h, w = len(rows), len(rows[0])
    return [
        ("PLAYPAL", b"".join(rgb(i) for i in range(256))),
        ("COLORMAP", bytes(range(256))*34),
        ("PNAMES", pack("I", 1) + name("BASE")),
        ("TEXTURE1", definitions([(label, w, h, [(0, 0, 0)]) for label in texture_names])),
        ("BASE", patch(rows)),
        ("F_START", b""),
        *[(label, bytes((x+3*y) % 256 for y in range(64) for x in range(64))) for label in flats],
        ("F_END", b""),
    ]


def replace(lumps, label, payload):
    return [(n, payload if n == label else data) for n, data in lumps]


class AssetTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.directory = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def run_cli(self, args, lumps, patches=(), ok=True):
        path = self.directory / "base.wad"
        path.write_bytes(wad(lumps))
        files = [path]
        for i, extra in enumerate(patches):
            p = self.directory / f"patch{i}.wad"
            p.write_bytes(wad(extra))
            files.append(p)
        result = subprocess.run([str(EXE), *map(str, args), *map(str, files)],
                                capture_output=True, text=True, timeout=15)
        if ok:
            self.assertEqual(result.returncode, 0, result.stderr)
        else:
            self.assertGreater(result.returncode, 0, result.stdout + result.stderr)
        return result

    def asset(self, lumps, kind="texture", label="WALL", patches=()):
        output = self.directory / "asset.ppm"
        self.run_cli(["asset", kind, label, output], lumps, patches)
        _, dimensions, _, pixels = output.read_bytes().split(b"\n", 3)
        width, height = map(int, dimensions.split())
        self.assertEqual(len(pixels), width*height*3)
        return width, height, pixels

    def render(self, lumps, camera=(0, 0, 25, 0), patches=()):
        output = self.directory / "frame.ppm"
        self.run_cli(["render-at", "E1M1", output, *camera], lumps, patches)
        return output.read_bytes().split(b"\n", 3)[3]

    @staticmethod
    def pixel(pixels, x, y, width=320):
        offset = (y*width+x)*3
        return pixels[offset:offset+3]

    def test_patch_posts_transparency_and_palette_255(self):
        rows = [[1, None, 255], [2, 3, None], [None, 4, 5]]
        width, height, pixels = self.asset(artwork(rows), "patch", "BASE")
        self.assertEqual((width, height), (3, 3))
        expected = b"".join(b"\xff\0\xff" if i is None else rgb(i) for row in rows for i in row)
        self.assertEqual(pixels, expected)

    def test_composite_clipping_transparency_and_patch_sprite_offsets(self):
        base = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
        overlay = [[20, None, 21], [22, 23, 24]]
        lumps = artwork(base)
        lumps = replace(lumps, "BASE", patch(base, left=-50, top=90))
        lumps = replace(lumps, "PNAMES", pack("I", 2)+name("BASE")+name("OVER"))
        lumps = replace(lumps, "TEXTURE1", definitions([("WALL", 3, 3, [(0, 0, 0), (-1, 1, 1)])]))
        lumps.append(("OVER", patch(overlay, left=100, top=-20)))
        _, _, pixels = self.asset(lumps)
        self.assertEqual(pixels, b"".join(rgb(i) for i in [1, 2, 3, 4, 21, 6, 23, 24, 9]))

    def test_overrides_palette_patch_and_texture_directory(self):
        lumps = artwork([[1]])
        _, _, pixels = self.asset(lumps, patches=[[("BASE", patch([[255]]))]])
        self.assertEqual(pixels, rgb(255))
        palette = b"".join(bytes((5, 6, 7)) for _ in range(256))
        _, _, pixels = self.asset(lumps, patches=[[("PLAYPAL", palette)]])
        self.assertEqual(pixels, b"\5\6\7")
        extra = [("TEXTURE1", definitions([("WALL", 2, 1, [(0, 0, 0), (1, 0, 0)])]))]
        self.assertEqual(self.asset(lumps, patches=[extra])[:2], (2, 1))

    def test_texture2_and_first_duplicate_definition(self):
        lumps = artwork([[1]]) + [("TEXTURE2", definitions([
            ("SECOND", 2, 1, [(0, 0, 0), (1, 0, 0)]), ("WALL", 4, 1, [(0, 0, 0)])]))]
        self.assertEqual(self.asset(lumps, label="SECOND")[:2], (2, 1))
        self.assertEqual(self.asset(lumps)[:2], (1, 1))

    def test_colormap_remaps_indices_before_palette_lookup(self):
        remap = bytes((255-i) for i in range(256))*32
        lumps = replace(artwork([[5]]), "COLORMAP", remap)
        self.assertEqual(self.asset(lumps)[2], rgb(250))

    def test_flat_exact_pixels_and_override(self):
        lumps = artwork()
        width, height, pixels = self.asset(lumps, "flat", "FLOOR")
        self.assertEqual((width, height), (64, 64))
        self.assertEqual(self.pixel(pixels, 4, 7, 64), rgb(25))
        self.assertEqual(self.asset(lumps, "flat", "FLOOR", [[("FLOOR", bytes([99])*4096)]])[2], rgb(99)*4096)

    def test_malformed_resources(self):
        cases = [
            ("PLAYPAL", b"\0"*767, "PLAYPAL"),
            ("PLAYPAL", b"\0"*769, "PLAYPAL"),
            ("COLORMAP", b"\0"*8191, "COLORMAP"),
            ("PNAMES", pack("I", 0xffffffff), "PNAMES"),
            ("TEXTURE1", pack("I", 0xffffffff), "TEXTURE1"),
            ("TEXTURE1", pack("II", 1, 0), "overlaps directory"),
            ("TEXTURE1", definitions([("WALL", 0, 1, [(0, 0, 0)])]), "dimensions"),
            ("TEXTURE1", definitions([("WALL", 1, 1, [(0, 0, 1)])]), "PNAMES index"),
            ("BASE", pack("HHhhI", 1, 1, 0, 0, 0), "overlaps header"),
            ("BASE", pack("HHhhI", 1, 1, 0, 0, 12)+bytes([0, 2, 0, 1, 2, 0, 255]), "height"),
        ]
        for label, payload, error in cases:
            with self.subTest(label=label, error=error):
                result = self.run_cli(["asset", "texture", "WALL", self.directory / "bad.ppm"],
                                      replace(artwork(), label, payload), ok=False)
                self.assertIn(error, result.stderr)

    def test_all_truncated_patch_prefixes_fail(self):
        data = patch([[1, None], [2, 255]])
        for cut in range(len(data)):
            with self.subTest(cut=cut):
                self.run_cli(["asset", "patch", "BASE", self.directory / "bad.ppm"],
                             replace(artwork(), "BASE", data[:cut]), ok=False)

    def test_missing_resource_and_bad_flat_fail_explicitly(self):
        for label in ("PLAYPAL", "COLORMAP", "PNAMES", "TEXTURE1", "BASE"):
            self.run_cli(["asset", "texture", "WALL", self.directory / "bad.ppm"],
                         [(n, b) for n, b in artwork() if n != label], ok=False)
        self.run_cli(["asset", "flat", "FLOOR", self.directory / "bad.ppm"],
                     replace(artwork(), "FLOOR", b"\0"*4095), ok=False)
        self.run_cli(["render", "E1M1", self.directory / "bad.ppm"], room(), ok=False)

    def test_wall_uv_offsets_and_bottom_pegging(self):
        rows = [[y+1]*8 for y in range(128)]
        lumps = room() + artwork(rows)
        normal = self.render(lumps)
        # At y=100, world z=24.8; ceiling 128 + row offset 16 gives v=119.
        self.assertEqual(self.pixel(normal, 160, 100), rgb(120))
        lines = bytearray(dict(lumps)["LINEDEFS"])
        struct.pack_into("<H", lines, 2*14+4, 17)
        pegged = self.render(replace(lumps, "LINEDEFS", bytes(lines)))
        # Bottom pegged: floor -16 + height 128 + row offset 16 gives v=103.
        self.assertEqual(self.pixel(pegged, 160, 100), rgb(104))
        stripes = [[x+1 for x in range(8)] for _ in range(128)]
        pattern = room() + artwork(stripes)
        self.assertEqual(self.pixel(self.render(pattern), 160, 100), rgb(1))
        sides = bytearray(dict(pattern)["SIDEDEFS"])
        struct.pack_into("<h", sides, 0, -7)
        self.assertEqual(self.pixel(self.render(replace(pattern, "SIDEDEFS", bytes(sides))), 160, 100), rgb(2))

    def test_floor_world_projection(self):
        pixels = self.render(room() + artwork(), (0, 0, 0, 0))
        # depth=16*160/99.5=25.7286, (floor(wx),floor(-wy)) = (25,0).
        self.assertEqual(self.pixel(pixels, 160, 199), rgb(25))

    def test_perspective_uv_and_near_plane_preserve_world_alignment(self):
        geom = replace(room(), "VERTEXES", b"".join(pack("hh", *v) for v in
                       [(-64, -64), (-64, 64), (64, 64), (128, -64)]))
        art = artwork([[x+1 for x in range(8)] for _ in range(128)])
        for angle, columns in [(0, (100, 160, 220)), (75, (260, 280, 300))]:
            with self.subTest(angle=angle):
                pixels = self.render(geom + art, (0, 0, 25, angle))
                # Independent ray/line intersection with the slanted east wall.
                # At 75 degrees one endpoint is behind the camera's near plane.
                a = math.radians(angle)
                for x in columns:
                    screen = (x+0.5-160)/160
                    dx = math.cos(a) + screen*math.sin(a)
                    dy = math.sin(a) - screen*math.cos(a)
                    slope = dy/dx
                    along = (64-64*slope)/(128+64*slope)
                    self.assertTrue(0 <= along <= 1)
                    u = -8 + along*math.hypot(64, 128)
                    self.assertEqual(self.pixel(pixels, x, 100), rgb(math.floor(u) % 8 + 1))

    def test_upper_and_lower_texture_pegging(self):
        art = artwork([[y+1]*8 for y in range(128)],
                      ("NEARWALL", "FARWALL", "UPPER", "LOWER"), ("FLOOR_A", "FLOOR_B", "CEILING"))
        geom = two_rooms()
        normal = self.render(geom + art)
        self.assertEqual(self.pixel(normal, 160, 20), rgb(120))
        self.assertEqual(self.pixel(normal, 160, 160), rgb(16))
        lines = bytearray(dict(geom)["LINEDEFS"])
        struct.pack_into("<H", lines, 2*14+4, 4+8+16)
        unpegged = self.render(replace(geom, "LINEDEFS", bytes(lines)) + art)
        self.assertEqual(self.pixel(unpegged, 160, 20), rgb(72))
        self.assertEqual(self.pixel(unpegged, 160, 160), rgb(128))

    def test_sky_portal_does_not_draw_upper_wall(self):
        art = artwork([[7]*8 for _ in range(128)],
                      ("NEARWALL", "FARWALL", "UPPER", "LOWER", "SKY1"), ("FLOOR_A", "FLOOR_B"))
        art = replace(art, "PNAMES", pack("I", 2)+name("BASE")+name("SKYPATCH"))
        defs = [(n, 8, 128, [(0, 0, 0)]) for n in ("NEARWALL", "FARWALL", "UPPER", "LOWER")]
        art = replace(art, "TEXTURE1", definitions(defs + [("SKY1", 8, 128, [(0, 0, 1)])]))
        art.append(("SKYPATCH", patch([[124]*8 for _ in range(128)])))
        geom = two_rooms()
        sectors = bytearray(dict(geom)["SECTORS"])
        for offset in (12, 26+12):
            sectors[offset:offset+8] = name("F_SKY1")
        pixels = self.render(replace(geom, "SECTORS", bytes(sectors)) + art)
        self.assertEqual(self.pixel(pixels, 160, 0), rgb(124))
        self.assertEqual(self.pixel(pixels, 160, 30), rgb(124))

    def test_sector_light_selects_real_colormap_rows(self):
        art = replace(artwork(), "COLORMAP", b"".join(bytes([32+i])*256 for i in range(32)))
        geom = room()
        sector = bytearray(dict(geom)["SECTORS"])
        struct.pack_into("<h", sector, 20, 255)
        bright = self.render(replace(geom, "SECTORS", bytes(sector)) + art)
        struct.pack_into("<h", sector, 20, 0)
        dark = self.render(replace(geom, "SECTORS", bytes(sector)) + art)
        self.assertEqual(self.pixel(bright, 160, 100), rgb(32))
        self.assertEqual(self.pixel(dark, 160, 100), rgb(63))

    def test_masked_portal_posts_show_far_wall_through_holes(self):
        names = ("NEARWALL", "FARWALL", "UPPER", "LOWER", "FENCE")
        art = artwork([[7]*8 for _ in range(128)], names, ("FLOOR_A", "FLOOR_B", "CEILING"))
        art = replace(art, "PNAMES", pack("I", 2)+name("BASE")+name("MASK"))
        defs = [(n, 8, 128, [(0, 0, 0)]) for n in names[:-1]] + [("FENCE", 8, 128, [(0, 0, 1)])]
        art = replace(art, "TEXTURE1", definitions(defs))
        art.append(("MASK", patch([[200 if x % 2 == 0 else None for x in range(8)] for _ in range(128)])))
        geom = two_rooms()
        sides = bytearray(dict(geom)["SIDEDEFS"])
        sides[20:28] = name("FENCE")
        pixels = self.render(replace(geom, "SIDEDEFS", bytes(sides)) + art)
        self.assertEqual(self.pixel(pixels, 160, 100), rgb(200))
        self.assertEqual(self.pixel(pixels, 163, 100), rgb(7))


if __name__ == "__main__":
    unittest.main(verbosity=2)

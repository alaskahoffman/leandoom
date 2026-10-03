"""Analytic two-room geometry tests; no external WAD or display is needed."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from test_wad import EXE, name, pack, room, wad


def two_rooms(closed=False, far_texture="FARWALL"):
    vertices = [(-64, -64), (-64, 64), (64, 64), (64, -64), (192, 64), (192, -64)]
    lines = [(0, 1, 1, 0, 65535), (1, 2, 1, 0, 65535), (2, 3, 4, 0, 1),
             (3, 0, 1, 0, 65535), (2, 4, 1, 1, 65535),
             (4, 5, 1, 1, 65535), (5, 3, 1, 1, 65535)]
    sides = b"".join(pack("hh", 0, 0) + name("UPPER") + name("LOWER") + name(tex) + pack("H", sec)
                     for sec, tex in [(0, "NEARWALL"), (1, far_texture)])
    sectors = b"".join(pack("hh", floor, ceiling) + name(flat) + name("CEILING") + pack("hHH", 220, 0, 0)
                       for floor, ceiling, flat in [(-16, 128, "FLOOR_A"), (16, 16 if closed else 48, "FLOOR_B")])
    segs = [(0, 1, 0, 0), (1, 2, 1, 0), (2, 3, 2, 0), (3, 0, 3, 0),
            (3, 2, 2, 1), (2, 4, 4, 0), (4, 5, 5, 0), (5, 3, 6, 0)]
    payloads = {
        "THINGS": pack("hhHHH", 0, 0, 0, 1, 7),
        "VERTEXES": b"".join(pack("hh", *v) for v in vertices),
        "LINEDEFS": b"".join(pack("7H", a, b, flags, 0, 0, front, back)
                              for a, b, flags, front, back in lines),
        "SIDEDEFS": sides,
        "SECTORS": sectors,
        "SEGS": b"".join(pack("6H", a, b, 0, line, side, 0) for a, b, line, side in segs),
        "SSECTORS": pack("4H", 4, 0, 4, 4),
        "NODES": pack("12h2H", 64, 64, 0, -128, 64, -64, -64, 64,
                      64, -64, 64, 192, 0x8000, 0x8001),
        "BLOCKMAP": pack("hhHH6H9H", -128, -128, 3, 2, *([10]*6), 0, *range(7), 65535),
    }
    return [(n, payloads.get(n, data)) for n, data in room()]


class RenderTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.directory = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def render(self, lumps, camera=None):
        path = self.directory / "map.wad"
        output = self.directory / "frame.ppm"
        path.write_bytes(wad(lumps))
        if camera is None:
            args = ["render-flat", "E1M1", output, path]
        else:
            args = ["render-flat-at", "E1M1", output, *camera, path]
        result = subprocess.run([str(EXE), *map(str, args)], capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        header, size, maximum, pixels = output.read_bytes().split(b"\n", 3)
        self.assertEqual((header, size, maximum), (b"P6", b"320 200", b"255"))
        self.assertEqual(len(pixels), 320 * 200 * 3)
        return pixels

    def pixel(self, data, x, y):
        offset = (y * 320 + x) * 3
        return data[offset:offset + 3]

    def test_room_fills_frame_without_cracks(self):
        pixels = self.render(room())
        self.assertTrue(all(pixels[i:i+3] != b"\0\0\0" for i in range(0, len(pixels), 3)))

    def test_spawn_matches_explicit_camera_and_is_repeatable(self):
        auto = self.render(two_rooms())
        explicit = self.render(two_rooms(), (0, 0, 25, 0))  # floor -16 + eye 41
        self.assertEqual(auto, explicit)
        self.assertEqual(auto, self.render(two_rooms()))

    def test_portal_has_analytically_correct_bands(self):
        pixels = self.render(two_rooms())
        # Projection: y = 100 - (height - 25) * 160 / distance.
        # Near opening at x=64: top 42.5, bottom 122.5.
        # Far wall at x=192: top 80.8333, bottom 107.5.
        # Pixel centers define half-open intervals.
        bands = [(0, 42), (42, 81), (81, 107), (107, 122), (122, 200)]
        colors = []
        for first, last in bands:
            band = {self.pixel(pixels, 160, y) for y in range(first, last)}
            self.assertEqual(len(band), 1, (first, last, band))
            colors.append(band.pop())
        self.assertEqual(len(set(colors)), 5)

    def test_closed_portal_occludes_far_wall(self):
        closed_a = self.render(two_rooms(closed=True, far_texture="AAA"))
        closed_b = self.render(two_rooms(closed=True, far_texture="ZZZ"))
        self.assertEqual(closed_a, closed_b)
        open_a = self.render(two_rooms(far_texture="AAA"))
        open_b = self.render(two_rooms(far_texture="ZZZ"))
        self.assertNotEqual(open_a, open_b)

    def test_bsp_back_side_and_near_plane(self):
        for camera in [(128, 0, 32, 180), (63, 0, 25, 0), (64, 0, 25, 0),
                       (0, 63, 25, 45), (0, -63, 25, -45)]:
            with self.subTest(camera=camera):
                pixels = self.render(two_rooms(), camera)
                self.assertTrue(all(pixels[i:i+3] != b"\0\0\0" for i in range(0, len(pixels), 3)))

    def test_turning_changes_view(self):
        east = self.render(two_rooms(), (0, 0, 25, 0))
        west = self.render(two_rooms(), (0, 0, 25, 180))
        self.assertNotEqual(east, west)

    def test_render_errors(self):
        path = self.directory / "map.wad"
        path.write_bytes(wad([(n, b"" if n == "THINGS" else data) for n, data in room()]))
        output = self.directory / "frame.ppm"
        for args in [("render", "E1M1", output, path),
                     ("render-at", "E1M1", output, "abc", 0, 25, 0, path),
                     ("render-at", "E1M1", output, 40000, 0, 25, 0, path),
                     ("render-at", "E1M1", self.directory / "bad.wad", 0, 0, 25, 0, path)]:
            result = subprocess.run([str(EXE), *map(str, args)], capture_output=True, timeout=10)
            self.assertGreater(result.returncode, 0)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)

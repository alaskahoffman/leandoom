"""Sprite projection/occlusion and player collision using independent tiny WADs."""
import unittest
import struct
import test_assets
from test_assets import artwork, patch, replace, rgb, definitions
from test_wad import room, pack, name
from test_render import two_rooms


def things(lumps, entries):
    return replace(lumps, "THINGS", b"".join(pack("hhHHH", *t) for t in entries))


def sectors(lumps, first=(-16, 128), second=(-16, 128)):
    old = dict(lumps)["SECTORS"]
    return replace(lumps, "SECTORS", pack("hh", *first) + old[4:26] + pack("hh", *second) + old[30:])


class ThingTests(unittest.TestCase):
    setUp = test_assets.AssetTests.setUp
    tearDown = test_assets.AssetTests.tearDown
    run_cli = test_assets.AssetTests.run_cli
    render = test_assets.AssetTests.render
    pixel = staticmethod(test_assets.AssetTests.pixel)

    def scene(self, entries, rows=None, label="STIMA0", left=8, top=32):
        return things(room(), entries) + artwork() + [(label, patch(rows or [[240]*16 for _ in range(32)], left, top))]

    def test_projection_offsets_transparency_and_opaque_255(self):
        rows = [[240]*8+[None]*4+[255]*4 for _ in range(32)]
        scene = self.scene([(48, 0, 0, 2011, 7)], rows)
        pixels = self.render(scene, (0, 0, 0, 0))
        baseline = self.render(things(scene, []), (0, 0, 0, 0))
        self.assertEqual(self.pixel(pixels, 145, 100), rgb(240))
        self.assertEqual(self.pixel(pixels, 165, 100), self.pixel(baseline, 165, 100))
        self.assertEqual(self.pixel(pixels, 180, 100), rgb(255))
        self.assertEqual(self.pixel(pixels, 132, 100), self.pixel(baseline, 132, 100))
        self.assertEqual(self.pixel(pixels, 145, 46), self.pixel(baseline, 145, 46))
        self.assertEqual(self.pixel(pixels, 145, 47), rgb(240))

    def test_hidden_behind_wall_and_outside_view(self):
        for pos in [(96, 0), (-48, 0), (0, 48)]:
            scene = self.scene([(*pos, 0, 2011, 7)])
            self.assertEqual(self.render(scene), self.render(things(scene, [])))

    def test_spawn_flag_filter(self):
        for flags in [0, 1, 4, 23]:
            scene = self.scene([(48, 0, 0, 2011, flags)])
            self.assertEqual(self.render(scene, (0, 0, 0, 0)), self.render(things(scene, []), (0, 0, 0, 0)))

    def test_all_eight_rotations(self):
        base = room() + artwork() + [(f"POSSA{i}", patch([[230+i]*16 for _ in range(32)], 8, 32)) for i in range(1, 9)]
        for angle in range(0, 360, 45):
            scene = things(base, [(48, 0, angle, 3004, 7)])
            expected = ((180-angle) % 360)//45 + 1
            self.assertEqual(self.pixel(self.render(scene, (0, 0, 0, 0)), 160, 100), rgb(230+expected))

    def test_paired_rotations_mirror_pixels_and_origin(self):
        base = room() + artwork() + [("POSSA0", patch([[201]*8 for _ in range(32)], 3, 32)),
            ("POSSA2A8", patch([[230]*4+[240]*4 for _ in range(32)], 3, 32))]
        straight = self.render(things(base, [(48, 0, 135, 3004, 7)]), (0, 0, 0, 0))
        mirror = self.render(things(base, [(48, 0, 225, 3004, 7)]), (0, 0, 0, 0))
        self.assertEqual(self.pixel(straight, 152, 100), rgb(230))
        self.assertEqual(self.pixel(straight, 173, 100), rgb(240))
        # Flipping reverses the source step; it does not mirror the patch origin.
        self.assertEqual(self.pixel(mirror, 152, 100), rgb(240))
        self.assertEqual(self.pixel(mirror, 173, 100), rgb(230))

    def test_nearest_sprite_wins_independent_of_thing_order(self):
        base = self.scene([], label="STIMA0") + [("MEDIA0", patch([[230]*16 for _ in range(32)], 8, 32))]
        entries = [(48, 0, 0, 2011, 7), (32, 0, 0, 2012, 7)]
        a = self.render(things(base, entries), (0, 0, 0, 0))
        b = self.render(things(base, entries[::-1]), (0, 0, 0, 0))
        self.assertEqual(a, b)
        self.assertEqual(self.pixel(a, 160, 100), rgb(230))

    def test_equal_scale_keeps_sector_insertion_order(self):
        base = self.scene([], label="STIMA0") + [("MEDIA0", patch([[230]*16 for _ in range(32)], 8, 32))]
        # Sector lists insert at the head. Stable scale sorting draws the first
        # map thing last for equal scales, so reversing spawn order changes it.
        entries = [(48,0,0,2011,7),(48,0,0,2012,7)]
        a = self.render(things(base,entries),(0,0,0,0))
        b = self.render(things(base,entries[::-1]),(0,0,0,0))
        self.assertEqual(self.pixel(a,160,100),rgb(240))
        self.assertEqual(self.pixel(b,160,100),rgb(230))

    def test_sprites_behind_and_in_front_of_masked_fence(self):
        names = ("NEARWALL", "FARWALL", "UPPER", "LOWER", "FENCE")
        art = artwork([[7]*8 for _ in range(128)], names, ("FLOOR_A", "FLOOR_B", "CEILING"))
        art = replace(art, "PNAMES", pack("I", 2)+name("BASE")+name("MASK"))
        defs = [(n, 8, 128, [(0, 0, 0)]) for n in names[:-1]] + [("FENCE", 8, 128, [(0, 0, 1)])]
        art = replace(art, "TEXTURE1", definitions(defs))
        art += [("MASK", patch([[200 if x % 2 == 0 else None for x in range(8)] for _ in range(128)])),
                ("STIMA0", patch([[240]*32 for _ in range(64)], 16, 64))]
        geom = sectors(two_rooms())
        sides = bytearray(dict(geom)["SIDEDEFS"])
        sides[20:28] = name("FENCE")
        geom = replace(geom, "SIDEDEFS", sides)
        behind = self.render(things(geom, [(128, 0, 0, 2011, 7)]) + art)
        # Original tangent-table rounding puts the odd (transparent) column
        # at x=160 and the even fence column at x=161.
        self.assertEqual(self.pixel(behind, 160, 100), rgb(240))
        self.assertEqual(self.pixel(behind, 161, 100), rgb(200))
        front = self.render(things(geom, [(32, 0, 0, 2011, 7)]) + art)
        self.assertEqual(self.pixel(front, 160, 100), rgb(240))
        self.assertEqual(self.pixel(front, 161, 100), rgb(240))

    def test_portal_lintel_hides_top_of_sprite(self):
        # A lower front ceiling produces SIL_TOP in R_StoreWallRange. A patch
        # unrealistically protruding through a lower *back* ceiling is not the
        # same clipping case in vanilla.
        geom = sectors(two_rooms(),first=(-16,32),second=(16,128))
        sides = bytearray(dict(geom)["SIDEDEFS"])
        sides[20:28] = name("-")
        art = artwork([[7]*8 for _ in range(128)], ("FARWALL", "UPPER", "LOWER"), ("FLOOR_A", "FLOOR_B", "CEILING"))
        art += [("STIMA0", patch([[240]*32 for _ in range(128)], 16, 128))]
        scene = things(replace(geom, "SIDEDEFS", sides), [(128, 0, 0, 2011, 7)]) + art
        pixels = self.render(scene)
        base = self.render(things(scene, []))
        self.assertEqual(self.pixel(pixels, 160, 30), self.pixel(base, 160, 30))
        self.assertEqual(self.pixel(pixels, 160, 100), rgb(240))

    def test_missing_rotation_and_bad_patch_fail_clearly(self):
        for label, data in [("POSSA1", patch([[1]])), ("POSSA0", b"bad")]:
            scene = things(room(), [(48, 0, 0, 3004, 7)]) + artwork() + [(label, data)]
            result = self.run_cli(["render", "E1M1", self.directory / "bad.ppm"], scene, ok=False)
            self.assertIn("sprite POSS", result.stderr)

    def test_patch_archive_overrides_sprite(self):
        scene = self.scene([(48, 0, 0, 2011, 7)])
        pixels = self.render(scene, (0, 0, 0, 0), [[("STIMA0", patch([[230]*16 for _ in range(32)], 8, 32))]])
        self.assertEqual(self.pixel(pixels, 160, 100), rgb(230))

    def test_fullbright_and_sector_lighting(self):
        base = self.scene([(48, 0, 0, 2011, 7)])
        # Vanilla makes a nearby sprite fully lit in the default bright sector.
        # A darker sector distinguishes ordinary lighting from fullbright.
        sector=bytearray(dict(base)['SECTORS']);struct.pack_into('<h',sector,20,96)
        base=replace(base,'SECTORS',bytes(sector))
        palette_maps = bytes(range(256)) + bytes([17]) * (33*256)
        base = replace(base, "COLORMAP", palette_maps)
        self.assertEqual(self.pixel(self.render(base, (0, 0, 0, 0)), 160, 100), rgb(17))
        base += [("COLUA0", patch([[240]*16 for _ in range(32)], 8, 32))]
        self.assertEqual(self.pixel(self.render(things(base, [(48, 0, 0, 2028, 7)]), (0, 0, 0, 0)), 160, 100), rgb(240))

    def test_ceiling_attached_sprite(self):
        # Type 49 is a 68-unit hanging body: feet at ceiling minus 68.
        scene = self.scene([(48, 0, 0, 49, 7)], [[240]*16 for _ in range(68)], "GOR1A0", 8, 68)
        pixels = self.render(scene, (0, 0, 90, 0))
        self.assertEqual(self.pixel(pixels, 160, 100), rgb(240))

    def walk(self, lumps, ticks=35, keys=2):
        result = self.run_cli(["walk", "E1M1", ticks, keys], lumps)
        line = next(line for line in result.stdout.splitlines() if line.startswith("position "))
        return tuple(map(float, line.split()[1:]))

    def start(self, lumps, x=0, y=0, angle=0, extras=()):
        return things(lumps, [(x, y, angle, 1, 7), *extras])

    def test_wall_radius_no_tunneling_even_running(self):
        for keys in [2, 514]:
            x, y, z, _ = self.walk(self.start(room()), keys=keys)
            self.assertGreater(x, 46)
            self.assertLessEqual(x, 48)
            self.assertLess(abs(y), 1)  # finesine[0] is 25, not zero; exact drift is C-checked in test_walking.
            self.assertEqual(z, -16)

    def test_slanted_wall_keeps_square_footprint_clear(self):
        scene = self.start(room())
        vertices = [(-64, -64), (-64, 64), (32, 64), (96, -64)]
        scene = replace(scene, "VERTEXES", b"".join(pack("hh", *v) for v in vertices))
        x, y, _, _ = self.walk(scene)
        # East boundary x + y/2 = 64; the square's leading corner adds 24.
        self.assertGreater(x, 44)  # projection slides south along the wall.
        self.assertLessEqual(x + y/2, 64 - 24)

    def test_slide_along_wall(self):
        x, y, _, _ = self.walk(self.start(room(), x=47), ticks=8, keys=18)
        self.assertLessEqual(x, 48)
        self.assertLess(y, -18)  # Momentum builds over several tics.

    def test_step_limit_and_headroom(self):
        for floor, ceiling, passable in [(8, 128, True), (9, 128, False), (-16, 39, False), (-16, 40, True)]:
            scene = self.start(sectors(two_rooms(), second=(floor, ceiling)))
            x, _, z, _ = self.walk(scene)
            self.assertEqual(x > 80, passable, (floor, ceiling, x))
            if passable:
                self.assertEqual(z, floor)

    def test_blocking_flag_on_open_portal(self):
        scene = sectors(two_rooms())
        lines = bytearray(dict(scene)["LINEDEFS"])
        struct.pack_into("<H", lines, 2*14+4, 5)
        x, _, _, _ = self.walk(self.start(replace(scene, "LINEDEFS", lines)))
        self.assertLessEqual(x, 48)

    def test_drop_uses_gravity_and_lands(self):
        scene = self.start(sectors(two_rooms(), second=(-80, 128)), x=80, angle=0)
        # Spawn on high west floor, then run east beyond the support footprint.
        scene = self.start(scene, x=40)
        early = self.walk(scene, ticks=14)
        self.assertGreater(early[2], -80)
        self.assertLess(early[3], 0)
        self.assertEqual(self.walk(scene, ticks=35)[2:], (-80, 0))

    def test_solid_things_block_but_pickups_do_not(self):
        for kind, blocked in [(3004, True), (2011, False)]:
            scene = self.start(room(), x=-40, extras=[(20, 0, 0, kind, 7)])
            x, _, _, _ = self.walk(scene)
            self.assertEqual(x < 0, blocked)

    def test_flying_keys_do_not_lift_walking_player(self):
        self.assertEqual(self.walk(self.start(room()), keys=128), (0, 0, -16, 0))

    def test_no_input_and_repeatable_ticks(self):
        scene = self.start(room())
        self.assertEqual(self.walk(scene, keys=0), (0, 0, -16, 0))
        self.assertEqual(self.walk(scene, ticks=5), self.walk(scene, ticks=5))


if __name__ == "__main__":
    unittest.main()

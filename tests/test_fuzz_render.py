"""Fuzz integration: palette-index reads, post masks, occlusion and draw order."""
import unittest
import test_assets
from test_assets import patch,replace,rgb
from test_power_render import scene,tables,mapped
from test_things import things


def fuzz_tables():
    data=bytearray(tables());data[6*256:7*256]=bytes([219])*256
    return bytes(data)


def weapons(color=77):
    # Only the left half of each post is opaque.
    return [(label,patch([[color]*4+[None]*4 for _ in range(8)],-154,-130))
            for label in ('PISGA0','PISGB0','PISGC0','PISFA0')]


class FuzzRenderTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    pixel=staticmethod(test_assets.AssetTests.pixel)

    def frame(self,geom,script='1:2,15:0',combat=True):
        out=self.directory/'fuzz.ppm'
        self.run_cli(['render-combat' if combat else 'render-sim','E1M1',script,out],geom)
        return out.read_bytes().split(b'\n',3)[3]

    def test_weapon_posts_ignore_source_color_and_preserve_holes(self):
        geom=replace(scene(2024),'COLORMAP',fuzz_tables())
        pixels=self.frame(geom+weapons(77))
        other=self.frame(geom+weapons(121))
        self.assertEqual(pixels,other)
        self.assertEqual(self.pixel(pixels,155,164),rgb(219))
        background=self.frame(geom,combat=False)
        self.assertEqual(self.pixel(pixels,160,164),self.pixel(background,160,164))

    def test_invisibility_overrides_inverse_map_and_blinks_back_to_opaque(self):
        geom=replace(scene(2024,extra=[(0,0,0,2022,7)]),'COLORMAP',fuzz_tables())+weapons()
        self.assertEqual(self.pixel(self.frame(geom),155,164),rgb(219))
        geom=replace(scene(2024),'COLORMAP',fuzz_tables())+weapons()
        # Invisibility count 128 uses the opaque path; 120 uses fuzz again.
        self.assertEqual(self.pixel(self.frame(geom,'1:2,1972:0'),155,164),rgb(mapped(0,77)))
        self.assertEqual(self.pixel(self.frame(geom,'1:2,1980:0'),155,164),rgb(219))

    def test_equal_rgb_colors_do_not_erase_distinct_framebuffer_indices(self):
        cmap=bytearray(bytes([6])*(34*256))
        cmap[6*256:7*256]=bytes([220])*256
        cmap[6*256+5]=219  # Index 5 looks identical but must NOT be sampled.
        palette=bytearray(b''.join(rgb(i) for i in range(256)))
        palette[5*3:5*3+3]=palette[6*3:6*3+3]
        geom=replace(replace(scene(2024),'COLORMAP',bytes(cmap)),'PLAYPAL',bytes(palette))
        self.assertEqual(self.pixel(self.frame(geom+weapons()),155,164),rgb(220))

    def test_spectre_uses_background_sprite_regardless_of_map_order(self):
        actors=[(70,0,0,58,7),(100,0,0,2018,7)]
        art=[(f'SARG{c}0',patch([[81]*16 for _ in range(64)],8,64)) for c in 'AB']
        art += [(f'ARM1{c}0',patch([[121]*16 for _ in range(64)],8,64)) for c in 'AB']
        a=replace(scene(2045,extra=actors),'COLORMAP',fuzz_tables())+art
        b=replace(scene(2045,extra=list(reversed(actors))),'COLORMAP',fuzz_tables())+art
        first=self.frame(a,combat=False)
        self.assertEqual(first,self.frame(b,combat=False))
        self.assertEqual(self.pixel(first,155,100),rgb(219))

    def test_spectre_behind_wall_does_not_change_frame(self):
        geom=replace(scene(2045,extra=[(256,0,0,58,7)]),'COLORMAP',fuzz_tables())
        geom += [(f'SARG{c}0',patch([[81]*16 for _ in range(64)],8,64)) for c in 'AB']
        plain=things(geom,[(0,0,0,1,7),(0,0,0,2045,7)])
        self.assertEqual(self.frame(geom,combat=False),self.frame(plain,combat=False))

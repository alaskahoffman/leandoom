"""Independent WAD colormaps exercise the actual simulation-to-frame path."""
import struct
import unittest
import test_assets
from test_assets import artwork, patch, replace, definitions, rgb
from test_wad import room, pack, name
from test_things import things
from test_render import two_rooms
from test_combat import combat_art


def mapped(row, index):
    # Deliberately not a visual inversion: the renderer must use the WAD bytes.
    return index ^ 0xA5 if row == 32 else (index * 3 + row * 7) % 256


def tables(count=34):
    return b''.join(bytes(mapped(row, index) for index in range(256)) for row in range(count))


def power_art():
    return [(prefix+frame+'0', patch([[91]*8 for _ in range(16)],4,16))
            for prefix, frames in [('PINV','ABCD'),('PVIS','AB'),('PINS','ABCD')] for frame in frames]


def scene(power=2022, extra=(), sky=False):
    geom = things(room(), [(0,0,0,1,7), (0,0,0,power,7), *extra])
    geom = replace(geom, 'VERTEXES', b''.join(pack('hh',x,y) for x,y in
                    [(-128,-128),(-128,128),(128,128),(128,-128)]))
    sec = bytearray(dict(geom)['SECTORS'])
    struct.pack_into('<hh',sec,0,0,96)
    if sky: sec[12:20]=name('F_SKY1')
    art=artwork([[41]*8 for _ in range(128)], ('WALL','SKY1') if sky else ('WALL',))
    art=replace(replace(art,'FLOOR',bytes([21])*4096),'CEIL',bytes([31])*4096)
    if sky:
        art=replace(art,'PNAMES',pack('I',2)+name('BASE')+name('SKYPATCH'))
        art=replace(art,'TEXTURE1',definitions([('WALL',8,128,[(0,0,0)]),('SKY1',8,128,[(0,0,1)])]))
        art.append(('SKYPATCH',patch([[51]*8 for _ in range(128)])))
    return replace(geom,'SECTORS',bytes(sec))+replace(art,'COLORMAP',tables())+power_art()


class PowerRenderTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    pixel=staticmethod(test_assets.AssetTests.pixel)

    def frame(self, geom, script='1:2,1:0', combat=False, patches=()):
        output=self.directory/'power.ppm'
        self.run_cli(['render-combat' if combat else 'render-sim','E1M1',script,output],geom,patches)
        return output.read_bytes().split(b'\n',3)[3]

    def test_inverse_and_infrared_cover_walls_floor_and_ceiling(self):
        for power,row in [(2022,32),(2045,1)]:
            with self.subTest(power=power):
                pixels=self.frame(scene(power))
                for y,index in [(0,31),(100,41),(199,21)]:
                    self.assertEqual(self.pixel(pixels,160,y),rgb(mapped(row,index)))

    def test_sky_retains_row_zero_during_both_powers(self):
        for power,row in [(2022,32),(2045,1)]:
            pixels=self.frame(scene(power,sky=True))
            self.assertEqual(self.pixel(pixels,160,0),rgb(mapped(0,51)))
            self.assertEqual(self.pixel(pixels,160,100),rgb(mapped(row,41)))

    def test_sprite_fullbright_and_transparency_under_fixed_map(self):
        geom=scene(extra=[(80,0,0,2018,7)])
        geom += [(f'ARM1{frame}0',patch([[81]*8+[None]*8 for _ in range(64)],8,64)) for frame in 'AB']
        for script in ['1:2,1:0','1:2,6:0']:
            pixels=self.frame(geom,script)
            self.assertEqual(self.pixel(pixels,150,100),rgb(mapped(32,81)))
            self.assertEqual(self.pixel(pixels,170,100),rgb(mapped(32,41)))

    def test_weapon_and_fullbright_muzzle_flash_use_fixed_map(self):
        weapons=[entry for entry in combat_art() if entry[0].startswith('PIS')]
        geom=scene()+weapons
        for script,index in [('1:2,15:0',230),('1:2,15:0,5:8192',233)]:
            pixels=self.frame(geom,script,combat=True)
            self.assertEqual(self.pixel(pixels,156,164),rgb(mapped(32,index)))

    def test_masked_wall_posts_keep_holes_and_use_fixed_map(self):
        geom=things(two_rooms(),[(0,0,0,1,7),(0,0,0,2022,7)])
        side=bytearray(dict(geom)['SIDEDEFS']);side[20:28]=name('FENCE')
        geom=replace(geom,'SIDEDEFS',bytes(side))
        labels=('NEARWALL','FARWALL','UPPER','LOWER')
        art=artwork([[41]*8 for _ in range(128)],labels,('FLOOR_A','FLOOR_B','CEILING'))
        art=replace(art,'PNAMES',pack('I',2)+name('BASE')+name('MASK'))
        art=replace(art,'TEXTURE1',definitions([(n,8,128,[(0,0,0)]) for n in labels]+[('FENCE',8,128,[(0,0,1)])]))
        art += [('MASK',patch([[200]*4+[None]*4 for _ in range(128)]))]
        pixels=self.frame(geom+replace(art,'COLORMAP',tables())+power_art())
        row=[self.pixel(pixels,x,100) for x in range(40,280)]
        self.assertIn(rgb(mapped(32,200)),row)
        self.assertIn(rgb(mapped(32,41)),row)

    def test_first_tic_and_expiry_restore_ordinary_lighting(self):
        geom=scene()
        normal=things(geom,[(0,0,0,1,7)])
        for script in ['1:2','1:2,922:0','1:2,1050:0']:
            self.assertEqual(self.frame(geom,script),self.frame(normal,script))
        self.assertNotEqual(self.frame(geom),self.frame(normal))

    def test_missing_inverse_row_is_explicit_and_patch_override_is_used(self):
        geom=replace(scene(),'COLORMAP',tables(32))
        self.frame(geom,'1:2')  # Ordinary rendering still supports 32-row WADs.
        result=self.run_cli(['render-sim','E1M1','1:2,1:0',self.directory/'missing.ppm'],geom,ok=False)
        self.assertIn('missing player effect row 32',result.stderr)
        custom=tables(32)+bytes([219])*256
        pixels=self.frame(geom,patches=[[('COLORMAP',custom)]])
        self.assertEqual(self.pixel(pixels,160,100),rgb(219))

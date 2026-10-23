"""Original column-cache quirks and passive spawn timing reach the framebuffer."""
import json
from pathlib import Path
import random
import struct
import subprocess
import tarfile
import unittest
import fidelity_reference as ref
from motion_reference import function
import test_assets
from test_assets import artwork, definitions, name, pack, patch, replace, rgb
from test_combat import arena

ROOT=Path(__file__).resolve().parents[1]

class TextureColumnTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    asset=test_assets.AssetTests.asset
    render=test_assets.AssetTests.render
    pixel=staticmethod(test_assets.AssetTests.pixel)

    def test_compositing_matches_original_cache_at_clipped_post_boundaries(self):
        spec=json.loads((ROOT/'tests/reference/tick-trace.json').read_text())
        archive=ROOT/'artifacts/reference/chocolate-doom-3.1.1-full.tar.gz'
        self.assertEqual(ref.digest(archive.read_bytes()),spec['archive_sha256'])
        with tarfile.open(archive) as tar:
            data=tar.extractfile(f'chocolate-doom-{spec["commit"]}/src/doom/r_data.c').read().decode()
        source='''#include <stdio.h>
#include <string.h>
typedef unsigned char byte;
typedef struct {byte topdelta,length,unused;} column_t;
'''+function(data,'void\nR_DrawColumnInCache')+'''
int main(void){int h,origin,top,count;while(scanf("%d%d%d%d",&h,&origin,&top,&count)==4){
byte column[260]={0},cache[128];memset(cache,37,sizeof cache);
column[0]=top;column[1]=count;column[count+4]=255;
for(int i=0;i<count;i++)column[3+i]=80+i;
R_DrawColumnInCache((column_t*)column,cache,origin,h);
for(int i=0;i<h;i++)printf("%s%d",i?" ":"",cache[i]);puts("");}return 0;}
'''
        c=self.directory/'cache.c';c.write_text(source)
        rng=random.Random(0xCA4E)
        cases=[(64,origin,top,count) for origin in [-40,-16,-1,0,1,48,64] for top,count in [(0,24),(7,31),(31,33)]]
        cases += [(rng.randrange(1,129),rng.randrange(-160,160),rng.randrange(64),rng.randrange(1,65)) for _ in range(40)]
        actual=[]
        for h,origin,top,count in cases:
            overlay=[[None]]*top+[[80+i] for i in range(count)]
            art=artwork([[37]]*h)
            art=replace(art,'PNAMES',pack('I',2)+name('BASE')+name('OVER'))
            art=replace(art,'TEXTURE1',definitions([('WALL',1,h,[(0,0,0),(0,origin,1)])]))
            art.append(('OVER',patch(overlay)))
            actual.append(self.asset(art)[2])
        for opt in ['-O0','-O2']:
            binary=self.directory/'cache'
            subprocess.run(['cc',opt,str(c),'-o',str(binary)],check=True,capture_output=True)
            expected=subprocess.run([str(binary)],input=''.join(' '.join(map(str,row))+'\n' for row in cases),text=True,capture_output=True,check=True).stdout.splitlines()
            for case,pixels,row in zip(cases,actual,expected):
                self.assertEqual(pixels,b''.join(rgb(int(i)) for i in row.split()),(opt,case))

    def test_short_wall_reads_post_padding_instead_of_height_wrapping(self):
        art=artwork([[102]*8 for _ in range(24)])
        data=bytearray(dict(art)['BASE'])
        for x in range(8):
            offset=struct.unpack_from('<I',data,8+4*x)[0]
            data[offset+3+24]=201  # Legal post trailing padding, not a texel.
        art=replace(art,'BASE',bytes(data))
        from test_wad import room
        geom=room();sector=bytearray(dict(geom)['SECTORS']);struct.pack_into('<h',sector,2,32)
        geom=replace(geom,'SECTORS',bytes(sector))
        sides=bytearray(dict(geom)['SIDEDEFS'])
        for i in range(len(sides)//30):struct.pack_into('<h',sides,i*30+2,0)
        geom=replace(geom,'SIDEDEFS',bytes(sides))
        pixels=self.render(geom+art,(0,0,25,0))
        self.assertEqual(self.pixel(pixels,160,141),rgb(102))
        self.assertEqual(self.pixel(pixels,160,143),rgb(201))

    def test_short_composite_reads_next_cached_column_and_skips_single_patch_columns(self):
        from test_wad import room
        geom=room();sector=bytearray(dict(geom)['SECTORS'])
        struct.pack_into('<h',sector,2,32)
        geom=replace(geom,'SECTORS',bytes(sector))
        sides=bytearray(dict(geom)['SIDEDEFS'])
        for i in range(len(sides)//30):struct.pack_into('<h',sides,i*30+2,0)
        geom=replace(geom,'SIDEDEFS',bytes(sides))
        # Original projection maps screen x=151 to texture column 60 (wrapped
        # to 4), and row 143 to texture row 24, just beyond this short column.
        for mixed in [False,True]:
            art=artwork([[101+x for x in range(8)] for _ in range(24)])
            if mixed:
                art=replace(art,'PNAMES',pack('I',3)+name('BASE')+name('A')+name('B'))
                art=replace(art,'TEXTURE1',definitions([('WALL',8,24,[(0,0,0),(4,0,1),(6,0,2)])]))
                art += [('A',patch([[202]]*24)),('B',patch([[203]]*24))]
                before,after=202,203  # Column 5 lives in a lump, not the cache.
            else:
                art=replace(art,'TEXTURE1',definitions([('WALL',8,24,[(0,0,0),(0,0,0)])]))
                before,after=105,106
            pixels=self.render(geom+art,(0,0,25,0))
            self.assertEqual(self.pixel(pixels,151,141),rgb(before),mixed)
            self.assertEqual(self.pixel(pixels,151,143),rgb(after),mixed)

    def test_passive_animation_uses_spawn_countdown_and_restarts(self):
        # Original RNG: player lastlook=8; bonus lastlook=109, duration=220%6+1=5.
        scene=arena(extras=[(96,0,0,2015,7)])+artwork([[1]*8 for _ in range(128)])
        for flat in ['FLOOR','CEIL']:scene=replace(scene,flat,bytes([2])*4096)
        scene += [(f'BON2{letter}0',patch([[220+i]*16 for _ in range(32)],8,32)) for i,letter in enumerate('ABCD')]
        for script,color in [('0:0',220),('4:0',220),('5:0',221),('10:0',221),('11:0',222),('17:0',223),('23:0',222),('29:0',221),('35:0',220),('4:0,1:0',221),('35:0,1:1024,4:0',220)]:
            out=self.directory/'anim.ppm'
            self.run_cli(['render-sim','E1M1',script,out],scene)
            pixels=out.read_bytes().split(b'\n',3)[3]
            # Tick zero has the initial view height, so inspect presence of the
            # unique sprite color rather than choosing a fixed camera row.
            colors={pixels[i:i+3] for i in range(0,len(pixels),3)}
            self.assertIn(rgb(color),colors,script)
            for other in set(range(220,224))-{color}:self.assertNotIn(rgb(other),colors,script)

    def test_combat_barrel_preserves_randomized_spawn_phase(self):
        from test_combat import combat_art
        scene=arena([(96,0,0,2035,7)])+combat_art(wall_rows=[[1]*8 for _ in range(128)])
        for flat in ['FLOOR','CEIL']:scene=replace(scene,flat,bytes([2])*4096)
        scene += [(f'BAR1{letter}0',patch([[220+i]*16 for _ in range(32)],8,32)) for i,letter in enumerate('AB')]
        scene += [(f'BEXP{letter}0',patch([[245]*16 for _ in range(32)],8,32)) for letter in 'ABCDE']
        # The third P_Random value is 220: initial tics = 220%6+1 = 5.
        for ticks,color in [(0,220),(4,220),(5,221),(10,221),(11,220),(16,220),(17,221)]:
            out=self.directory/'barrel.ppm'
            self.run_cli(['render-combat','E1M1',f'{ticks}:0',out],scene)
            pixels=out.read_bytes().split(b'\n',3)[3]
            colors={pixels[i:i+3] for i in range(0,len(pixels),3)}
            self.assertIn(rgb(color),colors,ticks)
            self.assertNotIn(rgb(441-color),colors,ticks)
        self.run_cli(['render-combat','E1M1','34:8192',out],scene)
        pixels=out.read_bytes().split(b'\n',3)[3]
        colors={pixels[i:i+3] for i in range(0,len(pixels),3)}
        self.assertIn(rgb(245),colors)  # Death states override the spawn loop.
        self.assertNotIn(rgb(220),colors)
        self.assertNotIn(rgb(221),colors)

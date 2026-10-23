"""Integer sprite, post and surface animation checks against original C."""
import random
import subprocess
import tempfile
import unittest
import fidelity_reference as ref
import render_sprite_reference as oracle
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

class SpriteReferenceTests(unittest.TestCase):
    def test_original_projection_posts_and_animation(self):
        rng=random.Random(0x5F17)
        signed=lambda n:(n+2**31)%2**32-2**31
        commands=[]
        for _ in range(2500):
            view=signed(rng.getrandbits(32));dx,dy=[rng.randrange(-2048*65536,2048*65536) for _ in range(2)]
            z,vz=[rng.randrange(-128*65536,128*65536) for _ in range(2)]
            width=rng.randrange(1,257);left=rng.randrange(-64,257);top=rng.randrange(-32,257)
            commands.append(f'sprite {view} {dx} {dy} {z} {vz} {width} {left} {top} {rng.randrange(2)} {signed(rng.getrandbits(32))}')
        for depth in [262143,262144,262145,48*65536,2048*65536]:
            for side in [-256*65536,-65536,0,65536,256*65536]:
                for flip in [0,1]:commands.append(f'sprite 0 {depth} {side} 0 1638400 16 3 32 {flip} -1073741824')
        for _ in range(1500):
            vh=rng.choice([168,200]);top=rng.randrange(0,128);count=rng.randrange(1,256-top)
            commands.append(f'post {rng.randrange(256,64*65536)} {rng.randrange(-256*65536,256*65536)} {vh} {top} {count} {rng.randrange(-1,vh)} {rng.randrange(vh+1)}')
        for tick in [0,1,7,8,9,16,17,24,25,1000]:
            for base in [0,1,2,7,59,100]:
                for n in [2,3,4]:
                    for i in range(base,base+n):commands.append(f'anim {tick} {base} {n} {i}')
        actual=ref.run_probe(ROOT/'.lake/build/bin/fidelity-probe',commands)
        with tempfile.TemporaryDirectory() as directory:
            for opt in ['-O0','-O2']:
                try:binary=oracle.build(directory,opt)
                except subprocess.CalledProcessError as e:self.fail(e.stderr)
                expected=subprocess.run([str(binary)],input='\n'.join(commands)+'\n',capture_output=True,text=True,check=True).stdout.splitlines()
                self.assertEqual(len(expected),len(actual))
                for cmd,a,b in zip(commands,actual,expected):self.assertEqual(a,b,cmd)


import test_assets
from test_assets import replace,artwork,patch,definitions,rgb
from test_combat import arena
from test_wad import pack,name
import struct

class SurfaceRenderingTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli
    render=test_assets.AssetTests.render
    pixel=staticmethod(test_assets.AssetTests.pixel)

    def test_directory_order_absolute_phase_tick_boundaries_and_restart(self):
        art=artwork()
        # Nonstandard middle names prove that directory intervals define cycles.
        art=replace(art,'PNAMES',pack('I',4)+b''.join(name(n) for n in ['BASE','P1','P2','P3']))
        art=replace(art,'TEXTURE1',definitions([('WALL',8,128,[(0,0,0)])]+[(n,8,128,[(0,0,i+1)]) for i,n in enumerate(['SLADRIP1','ODDTEX','SLADRIP3'])]))
        art += [(f'P{i+1}',patch([[51+i]*8 for _ in range(128)])) for i in range(3)]
        end=next(i for i,(n,_) in enumerate(art) if n=='F_END')
        art[end:end]=[(n,bytes([61+i])*4096) for i,n in enumerate(['NUKAGE1','ODDFLAT','NUKAGE3'])]
        geom=arena();sides=bytearray(dict(geom)['SIDEDEFS']);sides[20:28]=name('SLADRIP1')
        sectors=bytearray(dict(geom)['SECTORS']);sectors[4:12]=name('NUKAGE1')
        scene=replace(replace(geom,'SIDEDEFS',bytes(sides)),'SECTORS',bytes(sectors))+art
        initial=self.render(scene)
        self.assertEqual(self.pixel(initial,160,100),rgb(51))
        self.assertEqual(self.pixel(initial,160,190),rgb(61))
        captures={}
        for ticks in [1,8,9,16,17,24,25,1]:
            p=self.directory/'frame.ppm'
            self.run_cli(['render-sim','E1M1',f'{ticks}:0',p],scene)
            pixels=p.read_bytes().split(b'\n',3)[3]
            self.assertEqual(self.pixel(pixels,160,100),rgb(51+((ticks-1)//8+1)%3))
            self.assertEqual(self.pixel(pixels,160,190),rgb(61+((ticks-1)//8+2)%3))
            if ticks in captures:self.assertEqual(pixels,captures[ticks])
            captures[ticks]=pixels
        missing=[(n,b) for n,b in scene if n!='NUKAGE3']
        self.run_cli(['render-sim','E1M1','1:0',self.directory/'bad.ppm'],missing,ok=False)

    def test_single_patch_columns_ignore_vertical_origin_but_composites_apply_it(self):
        art=artwork([[y+1]*8 for y in range(128)])
        geom=arena()
        # The SKY1 regression: one patch at y=-8 must expose its original rows.
        a=self.render(geom+art)
        shifted=replace(art,'TEXTURE1',definitions([('WALL',8,128,[(0,-8,0)])]))
        b=self.render(geom+shifted)
        self.assertEqual(a,b)
        # Positive origins shift composite columns. Negative-origin clipping
        # has its own source-pointer quirk, covered against R_DrawColumnInCache.
        composite=replace(art,'TEXTURE1',definitions([('WALL',8,128,[(0,8,0),(0,8,0)])]))
        c=self.render(geom+composite)
        self.assertNotEqual(self.pixel(a,160,100),self.pixel(c,160,100))

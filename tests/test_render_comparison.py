"""Pixel-report integrity and sky mapping against unchanged original C."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import fidelity_reference as reference
from motion_reference import function

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import render_compare as rc


class PixelComparisonTests(unittest.TestCase):
    def test_sky_window_is_the_measured_normal_input_route(self):
        commands=rc.dc.scenario('sky-window')
        self.assertEqual(len(commands),183)
        self.assertEqual(rc.dc.decode_demo(rc.dc.encode_demo(commands)),commands)
        self.assertEqual(commands[0],[0,0,16384,0])

    def test_exact_and_one_pixel_difference_are_reported_without_tolerance(self):
        frame=bytes(64000*3)
        self.assertEqual(rc.compare_pixels(frame,frame)['status'],'exact')
        changed=bytearray(frame);changed[(170*320+31)*3+1]=1
        report=rc.compare_pixels(frame,changed)
        self.assertEqual(report['full']['different_pixels'],1)
        self.assertEqual(report['world_and_weapon']['different_pixels'],0)
        self.assertEqual(report['status_bar']['different_pixels'],1)
        self.assertEqual(report['first_difference'],dict(x=31,y=170,reference=[0,0,0],lean=[0,1,0]))
        self.assertEqual(rc.diff_ppm(frame,changed)[-64000*3:][(170*320+31)*3:(170*320+31)*3+3],bytes([255,0,0]))
        with self.assertRaises(ValueError):rc.compare_pixels(frame,frame[:-1])

    def test_malformed_or_partial_frame_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'frame.ppm'
            for content in [b'',b'P6\n320 200\n255\n',b'P6\n1 1\n255\n'+bytes(64000*3)]:
                p.write_bytes(content)
                with self.assertRaises(ValueError):rc.read_ppm(p)


class SkyMappingTests(unittest.TestCase):
    def test_original_integer_angle_table_and_sky_rows(self):
        sources=reference.sources()
        original=function(sources['src/doom/r_main.c'],'void R_InitTextureMapping')
        # Use the original fixed routines, not a floating-point reconstruction.
        fixed=sources['src/m_fixed.c']
        mul=function(fixed,'fixed_t\nFixedMul')
        div=function(fixed,'fixed_t FixedDiv')
        if 'FixedDiv2' in div:div=function(fixed,'fixed_t FixedDiv2')+'\n'+div
        tables=sources['src/tables.c']
        tangent=tables[tables.index('const fixed_t finetangent[4096]'):tables.index('const fixed_t finesine[')]
        program='''#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
typedef int32_t fixed_t;typedef uint32_t angle_t;
#define FRACBITS 16
#define FRACUNIT 65536
#define FINEANGLES 8192
#define FIELDOFVIEW 2048
#define ANGLETOFINESHIFT 19
#define ANG90 0x40000000u
static int centerx=160,centerxfrac=160*65536,viewwidth=320;
static int viewangletox[4096];static angle_t xtoviewangle[321],clipangle;
'''+mul+'\n'+div+'\n'+tangent+'\n'+original+'''
int main(void){R_InitTextureMapping();int32_t a;unsigned x,y,h;
 while(scanf("%d %u %u %u",&a,&x,&y,&h)==4)
 printf("%u %u %u\\n",xtoviewangle[x],((uint32_t)a+xtoviewangle[x])>>22,(100+y-h/2)&127);
}
'''
        cases=[]
        for a in [0,1,-1,0x40000000,0x7fffffff,-2147483648,-1073741824,0x13579bdf]:
            for x in range(321):
                for h,y in [(200,0),(200,100),(200,199),(168,0),(168,84),(168,167)]:cases.append((a,x,y,h))
        commands=['sky '+' '.join(map(str,c)) for c in cases]
        actual=reference.run_probe(ROOT/'.lake/build/bin/fidelity-probe',commands)
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory);(p/'sky.c').write_text(program)
            for opt in ['-O0','-O2']:
                result=subprocess.run(['cc',opt,'-fwrapv',str(p/'sky.c'),'-o',str(p/'sky')],capture_output=True,text=True)
                self.assertEqual(result.returncode,0,result.stderr)
                result=subprocess.run([str(p/'sky')],input=''.join(' '.join(map(str,c))+'\n' for c in cases),capture_output=True,text=True,check=True)
                self.assertEqual(actual,result.stdout.splitlines(),opt)


class ProjectionTests(unittest.TestCase):
    def test_wall_projection_and_plane_steps_against_original_c(self):
        import random
        import math
        import render_projection_reference as oracle
        rng=random.Random(0xD0011993)
        def signed(n):return (n+2**31)%2**32-2**31
        commands=[]
        # Fractional coordinates, all octants, near walls and clipped endpoints.
        for _ in range(2400):
            ax,ay,bx,by=[rng.randrange(-2048*65536,2048*65536) for _ in range(4)]
            angle=signed(int(math.atan2(by-ay,bx-ax)*2**32/(2*math.pi)) & 0xffff0000)
            commands.append(f'project {signed(rng.getrandbits(32))} {ax} {ay} {bx} {by} {angle} {rng.randrange(-128*65536,128*65536)}')
        for dist in [1,256,65535,65536,4*65536,64*65536,2048*65536]:
            for view in [0,1,-1,0x20000000,-0x20000000,0x40000000,-0x40000000]:
                commands.append(f'project {view} {dist} 4194304 {dist} -4194304 -1073741824 -524288')
        for vh in [168,200]:
            for y in [0,1,vh//2-1,vh//2,vh//2+1,vh-2,vh-1]:
                for x in [0,1,79,159,160,239,318,319]:
                    for height in [1,65535,65536,41*65536,512*65536]:
                        commands.append(f'plane {signed(rng.getrandbits(32))} {rng.randrange(-2048*65536,2048*65536)} {rng.randrange(-2048*65536,2048*65536)} {height} {vh} {y} {x}')
        actual=reference.run_probe(ROOT/'.lake/build/bin/fidelity-probe',commands)
        with tempfile.TemporaryDirectory() as directory:
            for opt in ['-O0','-O2']:
                binary=oracle.build(directory,opt)
                expected=subprocess.run([str(binary)],input='\n'.join(commands)+'\n',text=True,capture_output=True,check=True).stdout.splitlines()
                self.assertEqual(len(actual),len(expected))
                for command,a,b in zip(commands,actual,expected):self.assertEqual(a,b,f'{opt}: {command}')

    def test_packed_span_pixels_include_fraction_loss_wrap_and_cross_coordinate_carry(self):
        import random
        import render_projection_reference as oracle
        rng=random.Random(451)
        cases=[(0,-1,0,64,320),(0,0,0,-1,320),(-1,-1,65535,65535,320),
               (2147483647,-2147483648,-2147483648,2147483647,320)]
        cases += [tuple(rng.randrange(-2**31,2**31) for _ in range(4))+(rng.randrange(1,321),) for _ in range(300)]
        actual=reference.run_probe(ROOT/'.lake/build/bin/fidelity-probe',['span '+' '.join(map(str,c)) for c in cases])
        with tempfile.TemporaryDirectory() as directory:
            for opt in ['-O0','-O2']:
                binary=oracle.build(directory,opt)
                commands=['span '+' '.join(map(str,c))+f' {mode} 0' for c in cases for mode in [0,1]]
                expected=subprocess.run([str(binary)],input='\n'.join(commands)+'\n',text=True,capture_output=True,check=True).stdout.splitlines()
                for i,(case,line) in enumerate(zip(cases,actual)):
                    low=list(map(int,expected[2*i].split()));high=list(map(int,expected[2*i+1].split()))
                    self.assertEqual(list(map(int,line.split())),[a+256*b for a,b in zip(low,high)],f'{opt}: {case}')

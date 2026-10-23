"""HUD artwork integration and light tables extracted from pinned original C."""
import json
from pathlib import Path
import subprocess
import struct
import tempfile
import unittest
import fidelity_reference as reference
from motion_reference import function
import test_assets
from test_assets import patch, replace
from test_combat import arena, combat_art

ROOT=Path(__file__).resolve().parents[1]


def font(color=246):
    return [(f'STCFN{code:03}',patch([[color,None],[color,color]],-1,-1)) for code in range(33,96)]


class HudTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def scene(self,color=246):
        return arena(extras=[(0,0,0,2007,7)])+combat_art()+font(color)

    def state(self,script):
        path=self.directory/'state.json'
        self.run_cli(['combat','E1M1',script,path],self.scene())
        return json.loads(path.read_text())

    def frame(self,script,color):
        path=self.directory/'hud.ppm'
        self.run_cli(['render-combat','E1M1',script,path],self.scene(color))
        return path.read_bytes().split(b'\n',3)[3]

    def test_pickup_timeout_and_no_development_messages_on_hud(self):
        self.assertEqual(self.state('0:0')['hudMessageTicks'],0)
        s=self.state('1:2')
        self.assertEqual((s['hudMessage'],s['hudMessageTicks']),('Picked up a clip.',140))
        self.assertEqual(self.state('1:2,139:0')['hudMessageTicks'],1)
        self.assertEqual(self.state('1:2,140:0')['hudMessageTicks'],0)
        # A failed use notice must not replace the real pickup message.
        self.assertEqual(self.state('1:2,1:4096')['hudMessage'],'Picked up a clip.')

    def test_original_font_offsets_spacing_transparency_and_expiry(self):
        a=self.frame('1:2',246);b=self.frame('1:2',247)
        changed={(i%320,i//320) for i in range(320*200) if a[i*3:i*3+3]!=b[i*3:i*3+3]}
        expected=set();x=0
        for c in 'PICKED UP A CLIP.':
            if c==' ':x+=4;continue
            expected.update([(x+1,1),(x+1,2),(x+2,2)]);x+=2
        self.assertEqual(changed,expected)
        self.assertEqual(self.frame('1:2,140:0',246),self.frame('1:2,140:0',247))

    def test_present_font_requires_all_original_glyphs(self):
        scene=[(n,b) for n,b in self.scene() if n!='STCFN080']
        self.run_cli(['render-combat','E1M1','1:2',self.directory/'bad.ppm'],scene,ok=False)

    def test_world_flash_and_sector_lit_weapon_reach_framebuffer(self):
        scene=arena()+combat_art(wall_rows=[[1]*8 for _ in range(128)])
        sector=bytearray(dict(scene)['SECTORS']);struct.pack_into('<h',sector,20,128)
        scene=replace(scene,'SECTORS',bytes(sector))
        # Each colormap emits its row number, regardless of the texture index.
        scene=replace(scene,'COLORMAP',b''.join(bytes([i])*256 for i in range(34)))
        frames=[]
        for script in ['15:0','15:0,5:8192']:
            path=self.directory/'light.ppm'
            self.run_cli(['render-combat','E1M1',script,path],scene)
            frames.append(path.read_bytes().split(b'\n',3)[3])
        from test_assets import rgb
        pixel=test_assets.AssetTests.pixel
        # East/west-facing wall: sector 128 -> level 8 + vertical bias 1.
        # Original angle-table rounding puts this wall just below scale index
        # 10: index 9 selects row 24 - 9/2 = 20 (integer division).
        from render_projection_reference import evaluate
        _,scale=map(int,evaluate(['column 0 16777216 16777216 -1073741824 -524288 300 0'])[0].split())
        self.assertEqual(scale>>12,9)
        self.assertEqual(pixel(frames[0],300,100),rgb(20))
        self.assertEqual(pixel(frames[1],300,100),rgb(16)) # extra light +1
        self.assertEqual(pixel(frames[0],156,164),rgb(5)) # weapon: 28 - 47/2


class LightTableTests(unittest.TestCase):
    def test_original_c_tables_and_orientation_at_both_optimization_levels(self):
        source=reference.sources()
        z=function(source['src/doom/r_main.c'],'void R_InitLightTables')
        view=function(source['src/doom/r_main.c'],'void R_ExecuteSetViewSize')
        scale=view[view.index('    // Calculate the light levels to use'):view.rfind('}')]
        seg=function(source['src/doom/r_segs.c'],'void\nR_RenderMaskedSegRange')
        select=seg[seg.index('    lightnum ='):seg.index('    maskedtexturecol =')]
        program='''#include <stdint.h>
#include <stdio.h>
#define LIGHTLEVELS 16
#define MAXLIGHTSCALE 48
#define MAXLIGHTZ 128
#define NUMCOLORMAPS 32
#define SCREENWIDTH 320
#define FRACUNIT 65536
#define LIGHTZSHIFT 20
#define LIGHTSCALESHIFT 12
#define LIGHTSEGSHIFT 4
#define DISTMAP 2
static unsigned char colormaps[32*256],*zlight[16][128],*scalelight[16][48],**walllights;
static int FixedDiv(int a,int b){return (int)((int64_t)a*65536/b);}
'''+z+'\nstatic void scale_init(void) { int i,j,startmap,level,viewwidth=320,detailshift=0;\n'+scale+'''}
int main(void){
 R_InitLightTables();scale_init();
 int sector,extralight,orientation,index;unsigned distance;
 while(scanf("%d %d %d %d %u",&sector,&extralight,&orientation,&index,&distance)==5){
 struct {int lightlevel;} sec={sector},*frontsector=&sec;
 struct vertex {int x,y;} a={0,0},b={1,1};
 struct {struct vertex *v1,*v2;} line={&a,&b},*curline=&line;
 if(orientation<0)b.y=0;else if(orientation>0)b.x=0;
 int lightnum;
'''+select+'''
 if(lightnum<0)lightnum=0;if(lightnum>15)lightnum=15;
 if(index>47)index=47;unsigned zi=distance>>20;if(zi>127)zi=127;
 printf("%d %ld %ld\\n",lightnum,(long)(walllights[index]-colormaps)/256,(long)(zlight[lightnum][zi]-colormaps)/256);
 }
}
'''
        cases=[]
        # Every light boundary, all table entries, clamping, flash and orientation.
        for sector in [-32,-1,*range(256),256,287]:
            for extra in [0,1,2]:
                for orientation in [-1,0,1]:
                    for index in [0,1,15,46,47,48]:
                        cases.append((sector,extra,orientation,index,(index*3)<<20))
        for light in range(16):
            for index in range(48):cases.append((light*16,0,0,index,0))
            for index in range(129):
                for delta in [-1,0,1]:cases.append((light*16,0,0,0,max(0,(index<<20)+delta)))
        commands=['lighttables '+' '.join(map(str,c)) for c in cases]
        actual=reference.run_probe(ROOT/'.lake/build/bin/pickup-probe',commands)
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory);(p/'tables.c').write_text(program)
            for optimize in ['-O0','-O2']:
                subprocess.run(['cc',optimize,str(p/'tables.c'),'-o',str(p/'tables')],check=True,capture_output=True)
                result=subprocess.run([str(p/'tables')],input=''.join(' '.join(map(str,c))+'\n' for c in cases),text=True,capture_output=True,check=True)
                self.assertEqual(actual,result.stdout.splitlines(),optimize)

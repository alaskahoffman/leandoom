"""Exercise the actual DOS observer against controlled guest-memory snapshots.

This tests decoding and failure paths; real-executable integrations separately
check whether the pinned layout corresponds to original DOOM's running state.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import original_demo_compare as oc


def fixture_source():
    spec=oc.SPEC
    declarations='static const int ld_enemy_ids[] = {'+','.join(str(e['id']) for e in spec['enemy_profile'])+'};\n'
    declarations+='static const int ld_enemy_spawns[][5] = {'+','.join('{'+','.join(map(str,e['spawn']))+'}' for e in spec['enemy_profile'])+'};\n'
    declarations+='static const unsigned ld_enemy_types[] = {'+','.join(str(e['type']) for e in spec['enemy_profile'])+'};\n'
    for group in ['enemy','player','psprite','projectile']:
        prefix='ld_' if group=='enemy' else f'ld_{group}_'
        declarations+=''.join(f'static const unsigned {prefix}{k}={v};\n' for k,v in spec[group+'_offsets'].items())
    declarations+=''.join(f'static const unsigned ld_{k}={v};\n' for k,v in spec['player_layout'].items())
    declarations+=''.join(f'static const unsigned ld_shot_{k}={v};\n' for k,v in spec['projectile_layout'].items())
    observer=(ROOT/'tests/reference/dosbox_tick_trace.h').read_text().replace('/* ENEMY_PROFILE */',declarations)
    setup=''.join(f'put(code+{p},data+{t});\n' for p,t in spec['data_operands'].items())
    setup+=''.join(f'put(code+{p},code+{t});\n' for p,t in spec['code_operands'].items())
    setup+=''.join(f'ram[code+0x2081a+{i}]={b};\n' for i,b in enumerate(bytes.fromhex(spec['signature_hex'])))
    return r'''
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <initializer_list>
using PhysPt=uint32_t;
static unsigned char ram[32*1024*1024];
static struct {bool pmode=true;struct {bool big=true;} code;} cpu;
static struct {bool enabled=false;} paging;
enum {ds,cs};
static unsigned SegBase(int) {return 0;}
static unsigned SegValue(int s) {return s?8:16;}
static uint8_t mem_readb(PhysPt p) {if(p>=sizeof(ram)) std::exit(3);return ram[p];}
static uint16_t mem_readw(PhysPt p) {return mem_readb(p)|(mem_readb(p+1)<<8);}
static uint32_t mem_readd(PhysPt p) {return mem_readw(p)|(uint32_t(mem_readw(p+2))<<16);}
static void put(PhysPt p,uint32_t v) {for(unsigned i=0;i<4;++i)ram[p+i]=v>>(8*i);}
''' + observer + r'''
int main(int argc,char **argv) {
 const unsigned code=0x100000,data=0x200000,mo=0x300000,player=data+0x2ae78;
 const unsigned statebase=data+0x15a28,weapon=player+244,flash=weapon+16;
''' + setup + r'''
 put(player,mo);put(mo+132,player);
 put(data+0x12720,144);put(data+0x1271c,12);
 put(player+32,83);put(player+36,41);put(player+40,1);
 put(player+112,2);put(player+116,10);put(player+212,2);
 for(unsigned i=0;i<4;++i)put(player+156+4*i,5+i);
 put(weapon,statebase+22*28);put(weapon+4,7);put(weapon+8,12345);put(weapon+12,54321);
 put(flash,statebase+30*28);put(flash+4,0);put(player+200,3);put(player+232,1);
 put(data+0x2cf78,mo+0x200);
 for(unsigned j=0;j<6;++j) {
   unsigned a=mo+0x200+256*j;
   put(a+4,j==5?data+0x2cf74:a+256);put(a+8,code+0x31490);
   put(a+88,ld_enemy_types[j]);put(a+100,statebase+174*28);
   for(unsigned k=0;k<5;++k){unsigned v=uint16_t(ld_enemy_spawns[j][k]);ram[a+140+2*k]=v;ram[a+141+2*k]=v>>8;}
 }
 // Reverse pointer order deliberately: output must follow thinker links.
 const unsigned shot=0x304100,burst=0x304000;
 put(mo+0x200+256*5+4,shot);put(shot+4,burst);put(burst+4,data+0x2cf74);
 for(unsigned a : {shot,burst}) {
   put(a+8,code+0x31490);put(a+88,31);put(a+12,a==shot?123:456);
   put(a+16,uint32_t(-789));put(a+20,65536);put(a+56,uint32_t(-65536));put(a+60,8388608);
   put(a+96,3);put(a+136,2);
 }
 put(shot+100,statebase+97*28);put(shot+104,65536);put(shot+120,mo);
 put(shot+72,12);put(shot+76,uint32_t(-13));put(shot+80,uint32_t(-14));put(shot+32,0xf0000000);
 put(burst+100,statebase+99*28);put(burst+120,mo+0x200);
 const char *mode=argc>1?argv[1]:"good";
 if(!std::strcmp(mode,"misaligned"))put(weapon,statebase+1);
 if(!std::strcmp(mode,"outside"))put(flash,statebase+967*28);
 if(!std::strcmp(mode,"backlink"))put(mo+132,0);
 if(!std::strcmp(mode,"selection"))put(player+112,9);
 if(!std::strcmp(mode,"pending"))put(player+116,9);
 if(!std::strcmp(mode,"binding"))put(code+0x2d062,statebase+4);
 if(!std::strcmp(mode,"shot-source"))put(shot+120,0x305000);
 if(!std::strcmp(mode,"shot-state"))put(shot+100,statebase+1);
 if(!std::strcmp(mode,"shot-kind-state"))put(shot+100,statebase+174*28);
 if(!std::strcmp(mode,"exit-binding"))put(code+0x20d51,data+0x2b408);
 if(!std::strcmp(mode,"early-exit"))put(data+0x2b404,6);
 if(!std::strcmp(mode,"action"))put(data+0x2b404,9);
 LeanDoomObserve(code+0x2081a);
 put(data+0x2cf80,1);put(player+32,78);put(player+160,5);put(player+116,1);
 put(weapon,0);put(weapon+4,uint32_t(-1));put(flash,0);put(flash+4,uint32_t(-1));
 put(shot+8,uint32_t(-1)); // Removed thinker still linked pending next cleanup.
 put(burst+100,statebase+101*28);put(burst+96,1);
 put(data+0x2b404,6);
 if(!std::strcmp(mode,"secret-exit"))put(data+0x2b2f8,1);
 LeanDoomObserve(code+0x2082e);
 return 4; // Successful capture exits from the real observer.
}
'''


class DosPlayerObserverTests(unittest.TestCase):
    def test_actual_observer_decodes_fields_and_rejects_invalid_pointers(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory);source=p/'observer.cpp';binary=p/'observer'
            source.write_text(fixture_source())
            subprocess.run(['c++','-std=c++11','-O2',str(source),'-o',str(binary)],check=True,capture_output=True)
            env={**os.environ,'LEANDOOM_DOS_TRACE':str(p/'trace.jsonl'),
                 'LEANDOOM_DOS_BINDING':str(p/'binding.json'),'LEANDOOM_DOS_TICS':'1'}
            subprocess.run([str(binary),'good'],env=env,check=True,capture_output=True)
            rows=oc.read_records(p/'trace.jsonl',[[0,0,0,0]])
            self.assertFalse(rows[0]['state']['exitRequested'])
            self.assertTrue(rows[1]['state']['exitRequested'])
            player=rows[0]['state']['player'];weapon=rows[0]['state']['weapon']
            self.assertEqual(player,{**dict.fromkeys(oc.FIELDS,0),'health':83,'armor':41,'armorType':1,
                'readyWeapon':2,'pendingWeapon':None,'ammo':[5,6,7,8],'secrets':2})
            self.assertEqual(weapon,dict(state=22,tics=7,x=12345,y=54321,flashState=30,flashTics=0,refire=3,extraLight=1))
            self.assertEqual(rows[1]['state']['player'],{**player,'health':78,'ammo':[5,5,7,8],'pendingWeapon':1})
            self.assertEqual(rows[1]['state']['weapon'],{**weapon,'state':0,'tics':-1,'flashState':0,'flashTics':-1})
            flight=dict(x=123,y=-789,z=65536,momx=12,momy=-13,momz=-14,angle=0xf0000000,
                        floor=-65536,ceiling=8388608,state=97,tics=3,source=0,lastlook=2,missile=1)
            burst={**flight,'x':456,'momx':0,'momy':0,'momz':0,'angle':0,'state':99,'source':9,'missile':0}
            self.assertEqual(rows[0]['state']['projectiles'],[flight,burst])
            self.assertEqual(rows[1]['state']['projectiles'],[{**burst,'state':101,'tics':1}])
            for mode,message in [('misaligned','psprite state pointer'),('outside','psprite state pointer'),
                                 ('backlink','backlink'),('selection','weapon selection'),
                                 ('pending','weapon selection'),('binding','relocated data operands'),
                                 ('shot-source','projectile source'),('shot-state','state pointer'),
                                 ('shot-kind-state','imp fireball state'),
                                 ('exit-binding','relocated data operands'),('action','game action'),
                                 ('early-exit','final requested tic'),('secret-exit','exit must be normal')]:
                result=subprocess.run([str(binary),mode],env=env,capture_output=True,text=True)
                self.assertEqual(result.returncode,2,(mode,result.stderr))
                self.assertIn(message,result.stderr)

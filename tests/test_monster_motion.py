"""Original nonfloating monster/corpse momentum with explicit P_TryMove hooks."""
from pathlib import Path
import importlib.util
import itertools
import random
import subprocess
import tempfile
import unittest
import fidelity_reference
from motion_reference import function

ROOT=Path(__file__).resolve().parents[1]

def source():
    upstream=fidelity_reference.sources()
    support=(ROOT/'tests/reference/motion_fixture.c').read_text().split('#define NUMKEYS')[0]
    support=support.replace('int spawnstate;', 'int spawnstate,mass;')
    support=support.replace('int playerstate;','int playerstate,readyweapon;')
    support=support.replace('fixed_t ceilingz,height;','fixed_t ceilingz,height; int health;')
    old=function(support,'static boolean P_TryMove')
    support=support.replace(old,'''static unsigned outcomes;
static boolean P_TryMove(mobj_t *mo,fixed_t x,fixed_t y){
 assert(attempt_count<2);int accepted=(outcomes>>attempt_count)&1;
 attempts[attempt_count][0]=x;attempts[attempt_count++][1]=y;
 if(accepted){mo->x=x;mo->y=y;}return accepted;
}
''')
    head='''#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int fixed_t;typedef unsigned angle_t;
#define FRACBITS 16
#define FINEANGLES 8192
#define SLOPERANGE 2048
#define ANG90 0x40000000
#define ANG180 0x80000000
#define ANG270 0xc0000000
#define wp_chainsaw 7
'''
    fixed=upstream['src/m_fixed.c'];code=fixed[fixed.index('fixed_t\nFixedMul'):]
    tables=upstream['src/tables.c'];code+=tables[tables.index('int SlopeDiv('):tables.index('const byte gammatable')]
    main=upstream['src/doom/r_main.c'];code+='static fixed_t viewx,viewy;\n'
    code+=function(main,'angle_t\nR_PointToAngle\n')+function(main,'angle_t\nR_PointToAngle2')
    rng=upstream['src/doom/m_random.c'];start=rng.index('const unsigned char rndtable')
    code+=rng[start:rng.index('};',start)+2]+'\nstatic int prndindex;\n'+function(rng,'int P_Random')
    damage=function(upstream['src/doom/p_inter.c'],'void\nP_DamageMobj')
    code+='static void thrust(mobj_t *target,mobj_t *inflictor,mobj_t *source,int damage){unsigned ang;fixed_t thrust;\n'
    code+=function(damage,'    if (inflictor')+'}\n'
    mobj=upstream['src/doom/p_mobj.c']
    code+=function(mobj,'void P_XYMovement')+function(mobj,'void P_ZMovement')
    return head+support+code+'''
static int next(void){char *s=strtok(NULL," \\r\\n");assert(s);return (int)strtol(s,NULL,10);}
int main(int argc,char **argv){
 assert(argc==2);FILE *f=fopen(argv[1],"r");assert(f);char buf[1024];
 while(fgets(buf,sizeof(buf),f)){
  char *op=strtok(buf," \\r\\n");if(!op)continue;int v[16]={0};
  int count=!strcmp(op,"thrust")?16:14;for(int i=0;i<count;i++)v[i]=next();
  body=(mobj_t){0};
  if(!strcmp(op,"thrust")){
   mobjinfo_t info={.mass=v[5]};player_t playerSource={.readyweapon=v[12]?wp_chainsaw:1};
   mobj_t inflictor={.x=v[8],.y=v[9],.z=v[10]},source={.player=&playerSource};
   body=(mobj_t){.x=v[0],.y=v[1],.z=v[2],.health=v[3],.momx=v[6],.momy=v[7],.info=&info,.flags=v[11]?MF_NOCLIP:0};
   prndindex=v[13];thrust(&body,v[15]?&inflictor:NULL,v[14]?&source:NULL,v[4]);
   printf("%d %d %d\\n",body.momx,body.momy,prndindex);
  }else{
   sector_t sector={.floorheight=v[11]};subsector_t sub={&sector};
   body=(mobj_t){.x=v[0],.y=v[1],.z=v[2],.momx=v[3],.momy=v[4],.momz=v[5],.floorz=v[6],.ceilingz=v[7],.height=v[8],
    .flags=(v[9]?MF_CORPSE:0)|(v[10]?MF_NOGRAVITY:0),.subsector=&sub};outcomes=v[12];
   for(int i=0;i<v[13];i++){
    attempt_count=0;P_XYMovement(&body);if(body.z!=body.floorz||body.momz)P_ZMovement(&body);
    printf("%d %d %d %d %d %d %d",body.x,body.y,body.z,body.momx,body.momy,body.momz,attempt_count);
    for(int j=0;j<attempt_count;j++)printf(" %d %d",attempts[j][0],attempts[j][1]);puts("");
   }
  }
 }fclose(f);return 0;
}
'''

def corpus():
    commands=[]
    for seed,mass,damage,z,source,chainsaw in itertools.product(range(256),[100,400],[20,21,39,40],[64*65536,64*65536+1],[0,1],[0,1]):
        # chainsaw gate requires a present player source.
        commands.append('thrust '+' '.join(map(str,[1000,-2000,z,20,damage,mass,123,-456,-4000,5000,0,0,chainsaw,seed,source,1])))
    edges=[-2147483648,-1966081,-1966080,-983041,-16385,-16384,-4096,-4095,-1,0,1,4095,4096,16384,16385,983040,983041,1966080,1966081,2147483647]
    for mx,my,corpse,ledge,outcomes in itertools.product(edges,edges,[0,1],[0,1],[0,1,2,3]):
        commands.append('motion '+' '.join(map(str,[0,0,0,mx,my,0,0,128*65536,56*65536,corpse,0,-ledge*65536,outcomes,2])))
    rng=random.Random(0x4d4f4d)
    for _ in range(512):
        z=rng.randrange(-64*65536,256*65536);mz=rng.randrange(-20*65536,20*65536)
        commands.append('motion '+' '.join(map(str,[123,456,z,rng.choice(edges),rng.choice(edges),mz,0,rng.choice([8,128])*65536,56*65536,rng.randrange(2),rng.randrange(2),0,rng.randrange(4),24])))
    return commands

class MonsterMotionTests(unittest.TestCase):
    def test_original_thrust_and_xy_z_sequences(self):
        commands=corpus()
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder);(p/'commands').write_text('\n'.join(commands)+'\n');(p/'oracle.c').write_text(source())
            lean=subprocess.check_output([str(ROOT/'.lake/build/bin/monster-motion-probe'),str(p/'commands')])
            for opt in ['-O0','-O2']:
                compiled=subprocess.run(['cc','-std=c11','-fwrapv',opt,str(p/'oracle.c'),'-o',str(p/'oracle')],capture_output=True,text=True)
                self.assertEqual(compiled.returncode,0,compiled.stderr)
                original=subprocess.check_output([str(p/'oracle'),str(p/'commands')])
                if original!=lean:
                    for i,(a,b) in enumerate(zip(original.splitlines(),lean.splitlines())):
                        if a!=b:self.fail(f'{opt} output {i}: C {a!r}; Lean {b!r}')
                    self.fail('different output lengths')

    def test_runtime_masses_match_pinned_metadata(self):
        spec=importlib.util.spec_from_file_location('death_data',ROOT/'scripts/generate-death.py')
        data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
        _,_,metas,_=data.data()
        for kind,fields in metas:
            self.assertEqual(int(fields['mass']),400 if kind=='MT_SERGEANT' else 100)

"""Death view/turn branches against unchanged P_DeathThink and P_CalcHeight.

Weapon execution is a counted stub here; actual psprites, damage, movement,
attacker coordinates and presentation are covered by the recorded integration.
"""
import random
import subprocess
import tempfile
import unittest
from pathlib import Path
import fidelity_reference as ref
from motion_reference import function

ROOT = Path(__file__).resolve().parents[1]


def source():
    upstream = ref.sources()
    code = ref.oracle_source(upstream).split('int main(int argc, char **argv)')[0]
    code = code.replace('int playerstate; };', 'int playerstate; mobj_t *attacker; int damagecount; };')
    code += r'''
#define ANG5 (ANG90/18)
#define PST_REBORN 2
static unsigned target_angle;
static int psprite_calls;
static angle_t R_PointToAngle2(fixed_t x,fixed_t y,fixed_t tx,fixed_t ty) {
    (void)x;(void)y;(void)tx;(void)ty;return target_angle;
}
static void P_MovePsprites(player_t *p) {assert(p==&player);psprite_calls++;}
'''
    code += function(upstream['src/doom/p_user.c'], 'void P_DeathThink')
    code += r'''
int main(void) {
    char op[32],target[32];int a,d,h,dh,z,f,c,mx,my,t;
    while(scanf("%31s%d%31s%d%d%d%d%d%d%d%d%d",op,&a,target,&d,&h,&dh,&z,&f,&c,&mx,&my,&t)==12) {
        reset_motion();mobj_t killer={0};body.angle=(unsigned)a;
        body.z=z;body.floorz=f;body.ceilingz=c;body.momx=mx;body.momy=my;
        player.viewheight=h;player.deltaviewheight=dh;player.damagecount=d;player.playerstate=1;
        player.attacker=!strcmp(target,"none")?NULL:&killer;
        target_angle=(unsigned)strtol(target,NULL,10);leveltime=t;psprite_calls=0;
        P_DeathThink(&player);assert(psprite_calls==1);
        printf("%u %d %d %d %d %d\n",body.angle,player.damagecount,player.viewheight,
               player.deltaviewheight,player.viewz,player.bob);
    } return 0;
}
'''
    return code


class PlayerDeathTests(unittest.TestCase):
    def test_original_death_view_turn_and_flash_boundaries(self):
        rng=random.Random(0xDEAD)
        signed=lambda n:(n+2**31)%2**32-2**31
        step=0x40000000//18
        commands=[]
        for angle in [0,1,0x40000000,0x80000000,0xffffffff]:
            for delta in [0,1,step-1,step,step+1,0x80000000-1,0x80000000,
                          0x80000001,2**32-step-1,2**32-step,2**32-step+1,2**32-1,None]:
                for damage in [0,1,100]:
                    target='none' if delta is None else signed(angle+delta)
                    for height in [6*65536-1,6*65536,6*65536+1,7*65536,41*65536]:
                        commands.append(f'deathview {signed(angle)} {target} {damage} {height} -12345 0 0 8388608 0 0 100')
        for _ in range(1500):
            a=signed(rng.getrandbits(32));target=signed(rng.getrandbits(32)) if rng.randrange(4) else 'none'
            floor=rng.randrange(-128*65536,128*65536);z=floor+rng.choice([-1,0,1,20*65536])
            args=[a,target,rng.randrange(101),rng.randrange(6*65536,41*65536+1),rng.randrange(-65536,65536),
                  z,floor,floor+rng.randrange(8*65536,128*65536),rng.randrange(-30*65536,30*65536),
                  rng.randrange(-30*65536,30*65536),rng.randrange(100000)]
            commands.append('deathview '+' '.join(map(str,args)))
        actual=ref.run_probe(ROOT/'.lake/build/bin/fidelity-probe',commands)
        with tempfile.TemporaryDirectory() as tmp:
            c=Path(tmp)/'death.c';c.write_text(source());binary=c.with_suffix('')
            for opt in ['-O0','-O2']:
                subprocess.run(['cc',opt,'-fwrapv',str(c),'-o',str(binary)],check=True,capture_output=True,text=True)
                expected=subprocess.run([str(binary)],input='\n'.join(commands)+'\n',capture_output=True,text=True,check=True).stdout.splitlines()
                self.assertEqual(len(actual),len(expected))
                for cmd,a,b in zip(commands,actual,expected):self.assertEqual(a,b,(opt,cmd))

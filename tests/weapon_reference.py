"""Pinned original weapon routines: psprite sequencing and per-pellet random order.
Geometry, damage, actor animation and sound-device calls are supplied hooks.
"""
import argparse,hashlib,importlib.util,json,subprocess,tempfile
from pathlib import Path
from motion_reference import function
import fidelity_reference
ROOT=Path(__file__).resolve().parents[1]
SPEC=ROOT/'tests/reference/weapons.json'
PROBE=ROOT/'.lake/build/bin/weapon-probe'
spec=importlib.util.spec_from_file_location('weapon_data',ROOT/'scripts/generate-death.py')
data=importlib.util.module_from_spec(spec);spec.loader.exec_module(data)
def source():
    upstream=fidelity_reference.sources();rows,ids,_,_=data.data()
    selected=rows[:ids['S_SGUNFLASH2']+1]
    enums='enum {'+','.join(f'{r[-1]}={ids[r[-1]]}' for r in selected)+',S_PLAY=100,S_PLAY_ATK1,S_PLAY_ATK2,S_SAW};\n'
    sprites=sorted({r[0] for r in selected});enums+='enum {'+','.join(sprites)+'};\n'
    states='static state_t states[110]={\n'+''.join(f'[{name}]={{{spr},{frame},{tics},{{{action}}},{nxt},0,0}},\n' for spr,frame,tics,action,nxt,name in selected)+'};\n'
    pspr=upstream['src/doom/p_pspr.c']
    routines=''
    fixed=upstream['src/m_fixed.c'];routines+=function(fixed,'fixed_t\nFixedMul')
    tables=upstream['src/tables.c'];start=tables.index('const fixed_t finesine');end=tables.index(';',start);routines+=tables[start:end+1]+'\nstatic const fixed_t *finecosine=finesine+2048;\n'
    random=upstream['src/doom/m_random.c'];start=random.index('const unsigned char rndtable');routines+=random[start:random.index('};',start)+2]+'\n'
    routines+=function(random,'int P_Random')+function(random,'int P_SubRandom')
    for signature in ['void\nP_SetPsprite','void P_BringUpWeapon','boolean P_CheckAmmo','void P_FireWeapon','void P_DropWeapon','void\nA_WeaponReady','void A_ReFire','void\nA_Lower','void\nA_Raise','void\nA_Punch','static void DecreaseAmmo','void P_BulletSlope','void\nP_GunShot','void\nA_FirePistol','void\nA_FireShotgun\n','void A_Light0','void A_Light1','void A_Light2','void P_MovePsprites']:
        routines+=function(pspr,signature)
    return (ROOT/'tests/reference/weapon_fixture.c').read_text().replace('/* ENUMS */',enums).replace('/* STATES */',states).replace('/* ROUTINES */',routines)
def corpus():
    out=[]
    for w in range(3):
      for ammo in [0,1,2,8]:
       for owned in [0,1]:
        if w==2 and not owned:continue
        for seed in [0,1,87,255]:
         for mode in range(5):
          out.append(f'reset {w} {ammo} {ammo} {owned} {seed} {0xffffffff if seed==255 else seed*0x1000000}')
          for t in range(170):
            attack=int(mode==0 or t%31<7 or (mode==1 and t>60))
            choice=(t//11)%3 if mode==2 and t%11==0 else 9
            if mode==3 and t==20:out.append('die')
            out.append(f'tick {attack} {choice} {(t%17)*65536 if mode==4 else 0} {t%4}')
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
    commands=corpus();code=source()
    with tempfile.TemporaryDirectory(prefix='weapon-reference-') as tmp:
      d=Path(tmp);inp=d/'input';inp.write_text('\n'.join(commands)+'\n');c=d/'weapon.c';c.write_text(code)
      results=[]
      for opt in ['-O0','-O2']:
        exe=d/opt[1:];output=d/(opt[1:]+'.txt')
        subprocess.run(['cc','-std=c11',opt,'-fwrapv',str(c),'-o',str(exe)],check=True)
        subprocess.run([str(exe),str(inp),str(output)],check=True);results.append(output.read_bytes())
      assert results[0]==results[1],'C optimization mismatch'
      output=d/'lean.txt';subprocess.run([str(PROBE),str(inp),str(output)],check=True)
      actual=output.read_bytes()
      if actual!=results[0]:
        for i,(l,r) in enumerate(zip(actual.splitlines(),results[0].splitlines())):
          if l!=r:raise AssertionError(f'line {i}: {commands[i]}\nLean {l}\nC {r}')
        raise AssertionError('different lengths')
      source_names=['src/doom/p_pspr.c','src/doom/info.c','src/doom/m_random.c','src/m_fixed.c','src/tables.c']
      src=fidelity_reference.sources()
      result={'commit':'410d96855b5df5410ff591a90efeafa889119224','files':{n:hashlib.sha256(src[n].encode()).hexdigest() for n in source_names},'harness_sha256':hashlib.sha256(code.encode()).hexdigest(),'commands':len(commands),'sha256':hashlib.sha256(actual).hexdigest(),'bytes':len(actual),'profile':'Fist/pistol/shotgun original psprite actions; starts at ready. Supplied geometry/damage hooks consume 0..3 P_Random draws per pellet. Other weapons and full player thinker not covered.'}
      if a.record:SPEC.write_text(json.dumps(result,indent=2)+'\n')
      else:assert result==json.loads(SPEC.read_text())
      print(f"Original C -O0/-O2 and Lean agree: {len(commands)} weapon commands, {len(actual)} bytes")
if __name__=='__main__':main()

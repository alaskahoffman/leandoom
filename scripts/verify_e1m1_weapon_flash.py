#!/usr/bin/env python3
"""Connect quiet weapon countdowns through the flash phase to production Weapon.tick."""
import argparse,json,random,re,struct,subprocess
import verify_e1m1_flash_expiry as previous
ROOT,require=previous.ROOT,previous.require
NAMES=['seam_checked','quiet_checked','append_checked']
NAMES+=['Doom.Proofs.E1M1WeaponFlash.'+n for n in ['advance_inputs','suffix_correspondence','append','live_tick','weapon_summary','counted_read','countdown_flash','countdown_light','countdown_x','countdown_y','boundary_transport','tables_transport','live_correspondence']]

def certificate():
    return '''import Doom.Proofs.E1M1WeaponFlash
namespace Doom.Verification.ExtractedWeaponFlash
open Doom Doom.Proofs X86 X86Memory X86Control
 theorem seam_checked (s : X86Control.State) (p : Word) (v : Weapon.State)
    (pc : s.pc=0x2dc95) (h : E1M1WeaponFlash.Boundary s.core p v) (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables s.core.memory ∧ E1M1FlashExpiry.Separated p (s.core.regs 4)) :
    ∃ n t, n ≤ 110 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) :=
  E1M1WeaponFlash.suffix_correspondence s p v pc h supported expiry
 theorem quiet_checked (s : X86Memory.State) (f : Option Flags) (p : Word) (c : Weapon.Context)
    (h : E1M1WeaponFlash.Inputs s p c.state) (quiet : E1M1WeaponFlash.Quiet c.state)
    (supported : WeaponFlash.Supported c.state) (safe : E1M1WeaponFlash.Safe p (s.regs 4))
    (expiry : ¬ E1M1FlashUpdate.NoTransition c.state → E1M1FlashExpiry.Tables s.memory ∧ E1M1FlashExpiry.Separated p (s.regs 4)) :
    ∃ n t, n ≤ 125 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tick c).state :=
  E1M1WeaponFlash.live_correspondence s f p c h quiet supported safe expiry
 theorem append_checked (budget : Nat) (s u : X86Control.State) (p : Word) (v : Weapon.State)
    (earlier : ∃ n, n ≤ budget ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s u)
    (pc : u.pc=0x2dc95) (h : E1M1WeaponFlash.Boundary u.core p v) (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables u.core.memory ∧ E1M1FlashExpiry.Separated p (u.core.regs 4)) :
    ∃ n t, n ≤ budget+110 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n s t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) :=
  E1M1WeaponFlash.append budget s u p v earlier pc h supported expiry
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponFlash\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedWeaponFlash.'+short
        m=re.match(re.escape(f"'{n}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+n)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(out):
    import unicorn as u
    from unicorn import x86_const as x
    spec=json.loads((ROOT/'tests/reference/original-psprite-light.json').read_text())
    exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=previous.light.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
    raw=previous.light.extraction.extract(binary,exe,spec);tables=previous.light.table_data(binary,exe,spec)
    old=[previous.light.extraction.extract(binary,exe,json.loads((ROOT/'tests/reference'/name).read_text())) for name in ['original-weapon-drop.json','original-psprite-step.json','original-psprite-loop.json']]
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA,HEAP=0x100000,0x10000,0x600000
    for base,size in [(CODE,0x40000),(DATA,0x10000),(HEAP,0x4000)]:em.mem_map(base,size)
    for i in range(3):em.mem_write(CODE+0x2db40+16*i,raw['light'+str(i)])
    for pc,bs in [(0x2d040,old[0]['setter']),(0x2dc60,old[1]['psprite']),(0x2dc95,old[2]['tail'])]:em.mem_write(CODE+pc,bs)
    for name,bs in tables.items():
        bs=bytearray(bs)
        for r in spec['tables'][name]['relocations']:struct.pack_into('<I',bs,r['offset'],CODE+int(r['target'],16))
        em.mem_write(int(spec['tables'][name]['offset'],16),bytes(bs))
    rng=random.Random(0x244260);cases=[]
    for weapon in [0,10,18]:
      for wt in [0,1,2,3,7,0xffffffff,0x80000000,0x7fffffff]:
        if weapon and wt==1:continue
        for frame in [0,17,30,31]:
          for timer in [0,1,2,3,7,0xffffffff,0x80000000,0x7fffffff]:
            for alignment in range(4):cases.append((weapon,wt,frame,timer,*[rng.getrandbits(32) for _ in range(3)],alignment))
    def signed(v):return v if v<0x80000000 else v-0x100000000
    inp,outp=out/'inputs.txt',out/'live.txt'
    inp.write_text(''.join(' '.join(map(str,[c[0],signed(c[1]),c[2],*[signed(v) for v in c[3:7]]]))+'\n' for c in cases))
    subprocess.run([str(ROOT/'scripts/lake'),'env','lean','--run',str(ROOT/'tests/reference/weapon-flash-probe.lean'),str(inp),str(outp)],cwd=ROOT,check=True)
    live=[tuple(map(int,line.split())) for line in outp.read_text().splitlines()];require(len(live)==len(cases),'probe length')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    target=CODE+0x334a9;counts={'inactive':0,'permanent':0,'countdown':0,'expired':0}
    for i,(weapon,wt,frame,timer,light,wx,wy,align) in enumerate(cases):
        player=HEAP+0x100+align;sp=HEAP+0x3000+align
        em.mem_write(HEAP,rng.randbytes(0x4000))
        def put(a,v):em.mem_write(a,struct.pack('<I',v))
        def read(a):return struct.unpack('<I',em.mem_read(a,4))[0]
        for off,v in [(244,0 if weapon==0 else 0x15a28+28*weapon),(248,wt),(260,0 if frame==0 else 0x15a28+28*frame),(264,timer),(232,light),(252,wx),(256,wy)]:put(player+off,v)
        saved=[rng.getrandbits(32) for _ in range(5)];em.mem_write(sp,struct.pack('<6I',*saved,target))
        rr=[rng.getrandbits(32),player+244,rng.getrandbits(32),rng.getrandbits(32),sp,rng.getrandbits(32),0,player]
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2)
        em.emu_start(CODE+0x2dc6f,target,count=160)
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'return/{i}')
        require(em.reg_read(x.UC_X86_REG_ESP)==sp+24,f'stack/{i}')
        require(tuple(read(player+off) for off in [260,264,232,268,272])==live[i][:5],f'live fields/{i}: {cases[i]}')
        require(read(player+248)==live[i][5],f'weapon timer/{i}')
        require(live[i][6]==0,f'event reset/{i}')
        group='inactive' if frame==0 else 'permanent' if timer==0xffffffff else 'expired' if timer==1 else 'countdown'
        counts[group]+=1
    return dict(cases=len(cases),groups=counts,production_helper='Doom.Weapon.tick',scope='Quiet weapon slot plus all supported flash cases through RET versus production Weapon.tick; synthetic states. Weapon-timer and event-reset diagnostics supplement the formal five-flash-field result. Finite checks do not establish universal correspondence on their own.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    out=ROOT/'artifacts/e1m1-weapon-flash';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-flash-expiry')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponFlash'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    p=out/'Checked.lean';p.write_text(certificate())
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(out) if args.cross_check else None
    report=dict(audited_declarations=len(NAMES),axioms=checked.stdout.splitlines(),cross_check=native,
                scope='Quiet weapon countdown through all supported flash cases matches five flash fields of production Weapon.tick, under initial field/separation/table contracts. Action-triggering weapon transitions, full state and reachable-state correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: quiet weapon countdown and flash continuation match production Weapon.tick observations.')
if __name__=='__main__':main()

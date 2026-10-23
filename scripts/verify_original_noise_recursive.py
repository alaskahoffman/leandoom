#!/usr/bin/env python3
"""Certify recursive original sound execution and firing composition."""
import argparse,json,random,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['recursive_checked','alert_checked','fire_checked']
NAMES+=['Doom.Proofs.E1M1NoiseRecursive.'+n for n in ['dispatch_execution','execution','zero_fuel','alert_execution','fire_execution']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseRecursive
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedNoiseRecursive
open Doom Doom.Proofs X86 X86Memory X86Control
theorem recursive_checked (k : Nat) (phase : E1M1NoiseRecursive.Phase) (s t : X86Control.State)
    (pc : s.pc=phase.pc) (h : E1M1NoiseRecursive.eval k phase s=some t) :
    E1M1NoiseRecursive.Runs (E1M1NoiseRecursive.bound k) s t :=
  E1M1NoiseRecursive.execution k phase s t pc h
theorem alert_checked (k : Nat) (s t : X86Control.State) (pc : s.pc=0x27020)
    (h : E1M1NoiseRecursive.eval k .sector (NoiseAlert.result s.core)=some t) :
    E1M1NoiseRecursive.Runs (8+E1M1NoiseRecursive.bound k) s t :=
  E1M1NoiseRecursive.alert_execution k s t pc h
theorem fire_checked (k : Nat) (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (enough : E1M1WeaponFire.Enough s)
    (actor : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (attack : E1M1WeaponContinuation.AttackReturns s)
    (noise : E1M1NoiseRecursive.eval k .sector (NoiseAlert.result (E1M1NoiseAlert.noiseCall s).core)=some t)
    (ret : t.pc=0x2d44f) :
    E1M1NoiseRecursive.Runs (121+E1M1NoiseRecursive.bound k) ⟨s,f,0x2d410⟩ (WeaponFire.returned t.core t.flags) :=
  E1M1NoiseRecursive.fire_execution k s f t enough actor attack noise ret
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseRecursive\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseRecursive.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')



def cross_check(raw):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x27006);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(CODE,0x40000);em.mem_map(0,0x30000);em.mem_map(HEAP,0x3000);em.mem_map(0xfffff000,4096)
    for name,pc in [('sector',0x26f60),('traversal',0x26fa6),('opening',0x2c340)]:em.mem_write(CODE+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    depth=0;max_depth=0
    def visit(e,a,_n,_d):
        nonlocal depth,max_depth
        pc=a-CODE
        if pc==0x28000:e.emu_stop()
        else:
            visits.append(pc)
            if pc==0x26f60:depth+=1;max_depth=max(max_depth,depth)
            elif pc==0x27019:depth-=1
    em.hook_add(u.UC_HOOK_CODE,visit)
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    sx16=lambda v:v if v<0x8000 else v-0x10000
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    branches={k:0 for k in ['one_sided','closed','blocked','ordinary_call','blocking_call','fresh_child','improved_child','pruned_child','parent_continue','parent_done']}
    for i in range(2048):
        mode=i//1024;j=i%1024;align=j%4
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,0x13000,0x2b000,0x2c000,HEAP,HEAP+4096,HEAP+8192,0xfffff000]}
        def put(a,v,n=4):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a,n=4):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        sec=lambda k:HEAP+256+256*k+align
        line=lambda k:HEAP+4096+64*k+align
        sides=HEAP+1792+align
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=sec(0);rr[2]=0
        rr[4]=[HEAP+8192+3072+align,1,0xfffffff5][j%3]
        put(rr[4],CODE+0x28000);start=0x26f60
        for a,v in [(0x13580,7),(0x2b958,HEAP+3500),(0x2c118,sides)]:put(a,v)
        ends=[(0,1),(1,2),(2,0)] if mode==0 else [(0,1),(1,2),(0,2)]
        lists=[[0],[1],[2]] if mode==0 else [[0,2],[0,1],[1,2]]
        for k in range(3):
            ptr=HEAP+2304+16*k+align
            for a,v in [(sec(k),128 if k==2 and j%7==0 else 0),(sec(k)+4,128),
                        (sec(k)+66,6),(sec(k)+18,0),(sec(k)+22,0),(sec(k)+78,len(lists[k])),(sec(k)+82,ptr)]:put(a,v)
            for index,edge in enumerate(lists[k]):put(ptr+4*index,line(edge))
        for k,(a,b) in enumerate(ends):
            flags=68 if k==0 or (k==1 and j%3==0) else 4
            if k==2 and j%11==0:flags=0
            for address,value in [(line(k)+16,flags),(line(k)+22,(2*k)+65536*(2*k+1)),
                     (line(k)+46,sec(a)),(line(k)+50,sec(b)),
                     (sides+36*k+14,sec(a)),(sides+36*k+32,sec(b))]:put(address,value)
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear();depth=0
        em.emu_start(CODE+start,CODE+0x40000,count=1000)
        expected=[];n=0;flags=None
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        def push(v):rr[4]=(rr[4]-4)&mask;store(rr[4],v)
        def pop(r):rr[r]=get(rr[4]);rr[4]=(rr[4]+4)&mask
        def sector_prefix(is_child):
            nonlocal n
            for r in [3,1,6,7,5]:push(rr[r])
            rr[4]=(rr[4]-4)&mask;rr[3]=rr[0];rr[1]=rr[2];rr[2]=get(0x13580);n+=11
            old=get(rr[0]+66)
            if rr[2]==old:
                rr[0]=(rr[1]+1)&mask;n+=3
                if signed(rr[0])>=signed(get(rr[3]+18)):
                    if is_child:branches['pruned_child']+=1
                    return False
                if is_child:branches['improved_child']+=1
            elif is_child:branches['fresh_child']+=1
            rr[0]=get(0x13580);store(rr[3]+66,rr[0]);rr[0]=(rr[1]+1)&mask;rr[7]=get(rr[3]+78)
            store(rr[3]+18,rr[0]);rr[0]=get(0x2b958);rr[6]=0;store(rr[3]+22,rr[0]);n+=10
            return signed(rr[7])>0
        def sector_return():
            nonlocal n
            rr[4]=(rr[4]+4)&mask
            for r in [5,7,6,1,3]:pop(r)
            pc=get(rr[4])-CODE;rr[4]=(rr[4]+4)&mask;n+=7
            return pc
        def opening():
            nonlocal n
            rr[0]=rr[2];push(CODE+0x26fbb);n+=2
            for r in [3,1,2,6]:push(rr[r])
            rr[2]=rr[0];rr[0]=sx16(get(rr[0]+24,2))&mask;n+=8
            if rr[0]==mask:rr[2]=0;n+=2
            else:
                rr[0]=get(rr[2]+46);rr[2]=get(rr[2]+50);rr[3]=get(rr[0]+4);rr[1]=get(rr[2]+4);n+=6
                if signed(rr[3])>=signed(rr[1]):store(0x2c034,rr[1]);n+=1
                else:store(0x2c034,rr[3]);n+=2
                rr[3]=get(rr[0]);rr[6]=get(rr[2]);n+=4
                if signed(rr[3])<=signed(rr[6]):store(0x2c030,rr[6]);store(0x2c02c,rr[3]);n+=2
                else:store(0x2c030,rr[3]);store(0x2c02c,rr[6]);n+=3
                rr[2]=(get(0x2c034)-get(0x2c030))&mask;n+=2
            store(0x2c038,rr[2])
            for r in [6,2,1,3]:pop(r)
            ret=get(rr[4])-CODE;rr[4]=(rr[4]+4)&mask;n+=6
            require(ret==0x26fbb,'real opening return')
        def iteration():
            nonlocal n,flags
            rr[2]=get(rr[3]+82);rr[2]=get(rr[2]+rr[5]);n+=4
            if not get(rr[2]+16,1)&4:branches['one_sided']+=1
            else:
                opening();n+=2
                if signed(get(0x2c038))<=0:branches['closed']+=1
                else:
                    rr[0]=sx16(get(rr[2]+22,2))&mask;rr[0]=(rr[0]*18)&mask;rr[7]=get(0x2c118);rr[0]=(rr[0]+rr[7])&mask
                    store(rr[4],rr[7]);rr[7]=get(rr[0]+14);n+=8
                    if rr[3]==rr[7]:
                        rr[0]=sx16(get(rr[2]+24,2))&mask;rr[0]=(rr[0]*18)&mask;rr[0]=(rr[0]+get(rr[4]))&mask;rr[0]=get(rr[0]+14);n+=5
                    else:rr[0]=rr[7];n+=1
                    block=get(rr[2]+16,1)&64
                    call=True
                    if not block:rr[2]=rr[1];n+=4;branches['ordinary_call']+=1
                    elif rr[1]==0:rr[2]=1;n+=7;branches['blocking_call']+=1
                    else:n+=4;call=False;branches['blocked']+=1
                    if call:
                        push(CODE+0x27006)
                        require(recursive(True)==0x27006,'real recursive return')
            rr[6]=(rr[6]+1)&mask;rr[0]=get(rr[3]+78);rr[5]=(rr[5]+4)&mask;n+=5
            flags=cmpflags(rr[6],rr[0]);more=signed(rr[6])<signed(rr[0]);branches['parent_continue' if more else 'parent_done']+=1
            return more
        calls=0
        def recursive(is_child=False):
            nonlocal n,calls
            calls+=1;require(calls<100,'diagnostic call limit')
            if sector_prefix(is_child):
                rr[5]=0;n+=1
                while iteration():pass
            return sector_return()
        pc=recursive();flags=None
        require(depth==0,'balanced native recursive returns')
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        if flags is not None:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags/{i}')
    require(all(branches.values()),'missing branch coverage')
    require(max_depth>=4,'missing multi-level recursion')
    return dict(cases=2048,directed_cycle_cases=1024,bidirectional_cycle_cases=1024,max_native_call_depth=max_depth,branches=branches,all_registers=True,ordered_writes=True,mutable_memory_frame=True,wrapping_unaligned_stacks=True,comparison='independent Python summary; universal conditional execution proved by Lean')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-noise-recursive.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for dep in spec['byte_profiles']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/dep).read_text())))
    out=ROOT/'artifacts/original-noise-recursive';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-noise-iteration')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseRecursive'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate());r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: recursive sound execution, noise entry and accepted-fire return.')
if __name__=='__main__':main()

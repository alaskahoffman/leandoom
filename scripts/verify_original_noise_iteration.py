#!/usr/bin/env python3
"""Certify complete sound-line iterations and finite sector returns."""
import argparse,json,random,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['iteration_checked','loop_checked','sector_checked']
NAMES+=['Doom.Proofs.E1M1NoiseIteration.'+n for n in ['line_gate_pc','opening_block_pc','dispatched_pc','resumed_pc','result_pc','dispatch_execution','resume_execution','iteration_execution','loop_execution','progress','loop_return_execution','sector_execution']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseIteration
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedNoiseIteration
open Doom Doom.Proofs X86 X86Memory X86Control
theorem iteration_checked (s : X86Memory.State) (f : Option Flags) (h : E1M1NoiseIteration.Inputs s) :
    ∃ n, n≤95 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseIteration.program [] n ⟨s,f,0x26fa8⟩ (E1M1NoiseIteration.result s) :=
  E1M1NoiseIteration.iteration_execution s f h
theorem loop_checked (k : Nat) (s : X86Control.State) (h : E1M1NoiseIteration.LoopInputs k s) :
    ∃ n, n≤95*k ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseIteration.program [] n s (E1M1NoiseIteration.loop k s) :=
  E1M1NoiseIteration.loop_execution k s h
theorem sector_checked (k : Nat) (s : X86Memory.State) (f : Option Flags)
    (nonempty : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6)
    (inputs : E1M1NoiseIteration.LoopInputs k (E1M1NoiseIteration.started s))
    (done : (E1M1NoiseIteration.loop k (E1M1NoiseIteration.started s)).pc=0x27011) :
    ∃ n, n≤95*k+32 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseIteration.program [] n ⟨s,f,0x26f60⟩ (E1M1NoiseIteration.sectorResult k s) :=
  E1M1NoiseIteration.sector_execution k s f nonempty inputs done
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseIteration\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseIteration.'+short
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
    def visit(e,a,_n,_d):
        pc=a-CODE
        if (mode==1 and pc==0x28000) or (mode==0 and visits and pc in [0x26fa8,0x27011] and e.reg_read(x.UC_X86_REG_ESP)==initial_sp):e.emu_stop()
        else:visits.append(pc)
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
        parent=HEAP+256+align;child=HEAP+768+align;closed=HEAP+1280+align;sides=HEAP+1792+align;lines=HEAP+2304+align
        line=lambda k:HEAP+4096+64*k+align
        blocks=(j//5)%2;index=j%5
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=[HEAP+8192+3072+align,1,0xfffffff5][j%3];initial_sp=rr[4]
        for a,v in [(parent,0),(parent+4,128),(parent+66,6),(parent+78,5),(parent+82,lines),
                    (child,24),(child+4,96),(child+66,6),(child+18,0),(child+78,0),
                    (closed,128),(closed+4,128),(0x13580,7),(0x2b958,HEAP+3500),(0x2c118,sides),
                    (sides+14,parent),(sides+32,child),(sides+50,closed)]:put(a,v)
        for k in range(5):
            for a,v in [(lines+4*k,line(k)),(line(k)+16,0 if k==0 else 68 if k==2 else 4),
                        (line(k)+22,0x20000 if k==1 else 0x10000),(line(k)+46,parent),
                        (line(k)+50,closed if k==1 else child)]:put(a,v)
        if mode==0:
            rr[3]=parent;rr[1]=blocks;rr[6]=index;rr[5]=4*index
            # Include independently pruned calls in single-iteration tests.
            if j%3==0:put(child+66,7);put(child+18,blocks+1)
            start=0x26fa8
        else:rr[0]=parent;rr[2]=blocks;put(rr[4],CODE+0x28000);start=0x26f60
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
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
                        require(not sector_prefix(True),'child must be terminal')
                        require(sector_return()==0x27006,'real recursive return')
            rr[6]=(rr[6]+1)&mask;rr[0]=get(rr[3]+78);rr[5]=(rr[5]+4)&mask;n+=5
            flags=cmpflags(rr[6],rr[0]);more=signed(rr[6])<signed(rr[0]);branches['parent_continue' if more else 'parent_done']+=1
            return more
        if mode==0:pc=0x26fa8 if iteration() else 0x27011
        else:
            require(sector_prefix(False),'parent must have lines');rr[5]=0;n+=1
            for k in range(5):
                more=iteration();require(more==(k<4),'parent iteration count')
            pc=sector_return();flags=None
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        if flags is not None:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags/{i}')
    require(all(branches.values()),'missing branch coverage')
    return dict(cases=2048,iteration_cases=1024,whole_sector_cases=1024,lines_per_sector=5,branches=branches,all_registers=True,ordered_writes=True,mutable_memory_frame=True,modeled_flags=True,wrapping_unaligned_stacks=True,comparison='independent Python summary; universal conditional execution proved by Lean')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-noise-iteration.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for dep in spec['byte_profiles']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/dep).read_text())))
    out=ROOT/'artifacts/original-noise-iteration';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-noise-opening')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseIteration'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate());r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: complete line iteration, finite repetition and sector return.')
if __name__=='__main__':main()

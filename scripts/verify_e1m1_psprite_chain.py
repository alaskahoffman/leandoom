#!/usr/bin/env python3
"""Check action-free psprite chains and their complete flash-loop continuation."""
import argparse,json,re,random,struct,subprocess
import verify_e1m1_psprite_setter as previous
ROOT,require,extraction=previous.ROOT,previous.require,previous.extraction
NAMES=['chain_checked','mono_checked','complete_checked','slot_checked','suffix_checked']
NAMES+=['Doom.Proofs.E1M1PspriteChain.'+n for n in ['iteration_execution','chain_execution','chain_mono','complete_execution','slot_execution','finish_execution','suffix_execution']]

def certificate():
    s='''import Doom.Proofs.E1M1PspriteChain
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Verification.ExtractedPspriteChain
open Doom Doom.Proofs X86 X86Memory X86Control
 theorem chain_checked (fuel : Nat) (s t : X86Control.State) (ok : E1M1PspriteChain.chain fuel s=some t) :
    ∃ n, n ≤ 28*fuel+4 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteChain.program [] n s t :=
  E1M1PspriteChain.chain_execution fuel s t ok
 theorem mono_checked (fuel extra : Nat) (s t : X86Control.State) (ok : E1M1PspriteChain.chain fuel s=some t) :
    E1M1PspriteChain.chain (fuel+extra) s=some t :=
  E1M1PspriteChain.chain_mono fuel extra s t ok
 theorem complete_checked (fuel : Nat) (s : X86Memory.State) (f : Option Flags)
    (t : X86Control.State) (ok : E1M1PspriteChain.complete fuel s=some t) :
    ∃ n, n ≤ 28*fuel+13 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteChain.program [] n ⟨s,f,0x2d040⟩ t :=
  E1M1PspriteChain.complete_execution fuel s f t ok
 theorem slot_checked (fuel : Nat) (s : X86Memory.State) (f : Option Flags)
    (t : X86Control.State) (ok : E1M1PspriteChain.slot fuel s=some t) :
    ∃ n, n ≤ 28*fuel+28 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteChain.program [] n ⟨s,f,0x2dc6f⟩ t :=
  E1M1PspriteChain.slot_execution fuel s f t ok
 theorem suffix_checked (fuel : Nat) (s t : X86Control.State)
    (pc : s.pc=0x2dc95) (weaponIndex : s.core.regs 6=(0#32))
    (ok : E1M1PspriteChain.suffix fuel s=some t) :
    ∃ n, n ≤ 28*fuel+46 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteChain.program [] n s t :=
  E1M1PspriteChain.suffix_execution fuel s t pc weaponIndex ok
'''
    return s+'\n'+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedPspriteChain\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        n=short if '.' in short else 'Doom.Verification.ExtractedPspriteChain.'+short
        m=re.match(re.escape(f"'{n}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+n)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(setter,step,loop):
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA,HEAP=0x100000,0x10000,0x600000
    em.mem_map(CODE,0x40000);em.mem_map(DATA,0x10000);em.mem_map(HEAP,0x4000)
    for pc,raw in [(0x2d040,setter['setter']),(0x2dc60,step['psprite']),(0x2dc95,loop['tail'])]:em.mem_write(CODE+pc,raw)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes,visits,stops=[],[],set()
    def visit(e,a,_n,_d):
        if a in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v)))
    rng=random.Random(0x2d0aa);groups={};max_visits=0
    def zflags(v):return (0x40 if v==0 else 0)|(0x80 if v&0x80000000 else 0)
    for mode in ['setter_chain','flash_suffix']:
      for case in range(1024):
        blocks={DATA:bytearray(rng.randbytes(0x10000)),HEAP:bytearray(rng.randbytes(0x4000))};expected=[]
        rr=[rng.getrandbits(32) for _ in regs];align=case%4;player=HEAP+0x100+align;sp=HEAP+0x3000+align
        length=(case//4)%9;null_end=(case//36)%2==0
        def block(a):return DATA if DATA<=a<DATA+0x10000 else HEAP
        def read(a):return struct.unpack_from('<I',blocks[block(a)],a-block(a))[0]
        def put(a,v):struct.pack_into('<I',blocks[block(a)],a-block(a),v&0xffffffff)
        def write(a,v):put(a,v);expected.append((a,4,v&0xffffffff))
        def push(v):rr[4]=(rr[4]-4)&0xffffffff;write(rr[4],v)
        def pop(r):rr[r]=read(rr[4]);rr[4]+=4
        for i in range(1,length+1):
            state=0x15a28+i*28
            timer=0 if i<length or null_end else [1,7,0xffffffff,0x80000000][(case//72)%4]
            put(state+8,timer);put(state+12,0);put(state+16,i+1 if i<length else 0)
            put(state+20,0 if (case//144+i)%2==0 else rng.getrandbits(32) or 1);put(state+24,rng.getrandbits(32))
        rr[4]=sp;target=CODE+0x334a9
        if mode=='setter_chain':
            rr[0]=player;rr[2]=(case//288)%2;rr[3]=1 if length else 0;put(sp,target)
            entry=0x2d040;limit=28*(length+1)+13
        else:
            rr[1]=player+244;rr[6]=0;rr[7]=player
            saved=[rng.getrandbits(32) for _ in range(5)]
            struct.pack_into('<6I',blocks[HEAP],sp-HEAP,*saved,target)
            old=0x15a28+200*28;put(player+260,old);put(player+264,1);put(old+16,1 if length else 0)
            entry=0x2dc95;limit=28*(length+1)+46
        for base,data in blocks.items():em.mem_write(base,bytes(data))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear();stops.clear();stops.add(target)
        if mode=='flash_suffix':
            rr[6]+=1;rr[1]+=16;rr[3]=read(rr[1]);rr[2]=read(rr[1]+4)
            rr[3]=(rr[2]-1)&0xffffffff;write(rr[1]+4,rr[3])
            rr[3]=read(rr[1]);rr[0]=rr[7];rr[2]=rr[6];rr[3]=read(rr[3]+16);push(CODE+0x2dc95)
        push(rr[1]);push(rr[6]);rr[6]=rr[0];rr[0]=rr[3];rr[2]=(rr[2]<<4)&0xffffffff;rr[3]=(rr[6]+244+rr[2])&0xffffffff
        while True:
            wantflags=zflags(rr[0])
            if rr[0]==0:
                write(rr[3],0);break
            rr[0]=(rr[0]*28)&0xffffffff;rr[1]=(0x15a28+rr[0])&0xffffffff
            write(rr[3],rr[1]);rr[0]=read(rr[1]+8);write(rr[3]+4,rr[0]);rr[2]=read(rr[1]+20)
            if rr[2]:
                rr[0]=(rr[2]<<16)&0xffffffff;write(rr[3]+8,rr[0]);rr[0]=(read(rr[1]+24)<<16)&0xffffffff;write(rr[3]+12,rr[0])
            require(read(rr[1]+12)==0,'generated an action')
            rr[0]=read(rr[3]);rr[2]=read(rr[3]+4);rr[0]=read(rr[0]+16)
            wantflags=zflags(rr[2] if rr[2] else rr[0])
            if rr[2]:break
        pop(6);pop(1);rr[4]+=4
        if mode=='flash_suffix':
            rr[6]+=1;rr[1]+=16;wantflags=0x40
            rr[3]=read(rr[7]+252);write(rr[7]+268,rr[3]);rr[3]=read(rr[7]+256);write(rr[7]+272,rr[3])
            for r in [7,6,2,1,3]:pop(r)
            rr[4]+=4
        em.emu_start(CODE+entry,CODE+0x40000,count=limit+1)
        require(writes==expected,f'writes {mode}/{case}')
        for base,data in blocks.items():require(bytes(em.mem_read(base,len(data)))==bytes(data),f'memory {mode}/{case}')
        require([em.reg_read(r) for r in regs]==rr,f'registers {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'pc {mode}/{case}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==wantflags,f'flags {mode}/{case}')
        require(len(visits)<=limit,f'bound {mode}/{case}');max_visits=max(max_visits,len(visits))
      groups[mode]=1024
    return dict(cases=sum(groups.values()),groups=groups,max_instructions=max_visits,chain_lengths=[0,8],all_registers=True,modeled_flags=True,ordered_writes=True,full_data_memory=True,
                scope='Action-free setter chains and full flash-slot continuation through coordinate copy and RET. Synthetic state tables; action bodies and reachable-WAD invariants are not established.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    out=ROOT/'artifacts/e1m1-psprite-chain';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-psprite-setter')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PspriteChain'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe)
        raw=[extraction.extract(binary,exe,json.loads((ROOT/'tests/reference'/name).read_text())) for name in ['original-weapon-drop.json','original-psprite-step.json','original-psprite-loop.json']]
        native=cross_check(*raw)
    report=dict(audited_declarations=len(NAMES),axioms=checked.stdout.splitlines(),cross_check=native,
                scope='Successful bounded action-free chains refine original instruction prefixes and include real returns. Callbacks and fuel exhaustion fail. Initial invariants, action bodies and whole-game correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout,end='')
    print('PASS: action-free state chains, complete setter returns, and flash-loop composition.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify original sound-line guards, terminal recursive calls and returns."""
import argparse,json,random,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['traversal_checked','machine_checked','child_checked']
NAMES+=['Doom.Proofs.NoiseTraversal.'+n for n in ['decoded','initialize_execution','line_execution','opening_call_execution','opening_gate_execution','block_execution','advance_execution','return_execution']]
NAMES+=['Doom.Proofs.E1M1NoiseTraversal.'+n for n in ['contains_traversal','contains_prior','first_line_execution','opening_execution','skip_line_execution','terminal_sector_execution','child_execution','fire_return_execution']]
def certificate(raw):
    s='import Doom.Proofs.E1M1NoiseTraversal\nset_option maxRecDepth 32768\nnamespace Doom.Verification.ExtractedNoiseTraversal\nopen Doom Doom.Proofs X86 X86Memory X86Control\n'
    s+='def traversal : List UInt8 := ['+','.join(hex(v) for v in raw['traversal'])+']\ntheorem traversal_checked : traversal=NoiseTraversal.code := by decide\n'
    s+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (NoiseTraversal.bytesProgram traversal) [0x26f60,0x27006] 7 ⟨s,f,0x26fee⟩=some (NoiseTraversal.blockResult s) := by
  rw [traversal_checked]; exact NoiseTraversal.block_execution s f
 theorem child_checked (s : X86Memory.State) (f : Option Flags)
    (call : (NoiseTraversal.blockResult s).pc=0x26f60)
    (terminal : (E1M1NoiseAlert.sectorResult (NoiseTraversal.blockResult s).core).pc=0x27011)
    (ret : (E1M1NoiseTraversal.childReturn s).pc=0x27006) :
    ∃ n, n≤43 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseTraversal.program [] n ⟨s,f,0x26fee⟩
      (NoiseTraversal.advanced (E1M1NoiseTraversal.childReturn s).core) :=
  E1M1NoiseTraversal.child_execution s f call terminal ret
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseTraversal\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseTraversal.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Diagnostic x86/model comparison; the universal claims are Lean theorems."""
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x26fa6);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(CODE,0x40000);em.mem_map(0,0x30000);em.mem_map(HEAP,4096);em.mem_map(0xfffff000,4096)
    prior=json.loads((ROOT/'tests/reference/original-noise-alert.json').read_text())
    em.mem_write(CODE+0x26f60,bytes.fromhex(prior['units']['sector']['hex']))
    em.mem_write(CODE+0x26fa6,raw['traversal'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];stops=set();returned=False
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        nonlocal returned
        pc=a-CODE
        if mode==5 and pc==0x27006:returned=True
        if pc in stops and (mode!=5 or returned):e.emu_stop()
        else:visits.append(pc)
    em.hook_add(u.UC_HOOK_CODE,visit)
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    logical=lambda v:(int(v==0)<<6)|((v>>31)<<7)
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    branches={k:0 for k in ['one_sided','opening_call','closed','open','ordinary_call','first_block','blocked','loop','done','pruned_child','leaf_child']}
    for i in range(3072):
        mode=i//512;j=i%512
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,0x13000,0x2b000,0x2c000,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate((v&mask).to_bytes(4,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(4)),'little')
        rr=[rng.getrandbits(32) for _ in regs]
        rr[4]=[HEAP+3072+j%4,1,0xfffffff5][j%3]
        parent=HEAP+128+j%4;child=HEAP+512+j%4;line=HEAP+1024+j%4;lines=HEAP+1536+j%4
        edges=[0,1,0x7fffffff,0x80000000,0xffffffff,rng.getrandbits(32)]
        rr[3]=parent;rr[0]=child;rr[2]=line;rr[1]=edges[j%6];rr[5]=edges[(j//6)%6];rr[6]=edges[(j//36)%6]
        put(parent+78,edges[(j//4)%6]);put(parent+82,lines);put(lines,line)
        flag=[0,4,64,68,255,128][j%6]
        if mode==5:
            flag=64 if j%2 else 0
            if flag:rr[1]=0
        put(line+16,flag);put(0x2c038,edges[j%6]);put(0x13580,7);put(0x2b958,HEAP+2048)
        put(child+66,7 if j%3==0 else 6);put(child+18,0x80000000);put(child+78,0)
        starts=[0x26fa6,0x26fbb,0x26fee,0x27006,0x27011,0x26fee]
        stops=[{0x2c340,0x27006},{0x26fc4,0x27006},{0x26f60,0x27006},{0x26fa8,0x27011},{0x28000},{0x26fa8,0x27011}][mode]
        if mode==4:put(rr[4]+24,CODE+0x28000)
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear();returned=False
        em.emu_start(CODE+starts[mode],CODE+0x40000,count=60)
        expected=[];n=0;flags=None
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        def push(v):rr[4]=(rr[4]-4)&mask;store(rr[4],v)
        def restore():
            rr[4]=(rr[4]+4)&mask
            for r in [5,7,6,1,3]:rr[r]=get(rr[4]);rr[4]=(rr[4]+4)&mask
            pc=get(rr[4])-CODE;rr[4]=(rr[4]+4)&mask
            return pc
        if mode==0:
            rr[5]=0;rr[2]=get(rr[3]+82);rr[2]=get(rr[2]+rr[5]);v=get(rr[2]+16)&4;flags=0 if v else 0x40;n=5
            if v:
                rr[0]=rr[2];push(CODE+0x26fbb);pc=0x2c340;n+=2;branches['opening_call']+=1
            else:pc=0x27006;branches['one_sided']+=1
        elif mode==1:
            gap=get(0x2c038);flags=cmpflags(gap,0);n=2;pc=0x27006 if signed(gap)<=0 else 0x26fc4
            branches['closed' if signed(gap)<=0 else 'open']+=1
        elif mode in [2,5]:
            block=get(rr[2]+16)&64
            if not block:rr[2]=rr[1];flags=0x40;push(CODE+0x27006);pc=0x26f60;n=4;branches['ordinary_call']+=1
            elif rr[1]==0:rr[2]=1;flags=0x40;push(CODE+0x27006);pc=0x26f60;n=7;branches['first_block']+=1
            else:flags=logical(rr[1]);pc=0x27006;n=4;branches['blocked']+=1
            if mode==5:
                require(pc==0x26f60,'joined case must actually call')
                for r in [3,1,6,7,5]:push(rr[r])
                rr[4]=(rr[4]-4)&mask;rr[3]=rr[0];rr[1]=rr[2];rr[2]=get(0x13580);n+=11
                old=get(rr[0]+66);update=True
                if rr[2]==old:
                    rr[0]=(rr[1]+1)&mask;n+=3
                    if signed(rr[0])>=signed(get(rr[3]+18)):update=False
                if update:
                    rr[0]=get(0x13580);store(rr[3]+66,rr[0]);rr[0]=(rr[1]+1)&mask;rr[7]=get(rr[3]+78)
                    store(rr[3]+18,rr[0]);rr[0]=get(0x2b958);rr[6]=0;store(rr[3]+22,rr[0]);n+=10
                    require(signed(rr[7])<=0,'child must be terminal');branches['leaf_child']+=1
                else:branches['pruned_child']+=1
                pc=restore();n+=7;require(pc==0x27006,'real recursive return')
        if mode in [3,5]:
            rr[6]=(rr[6]+1)&mask;rr[0]=get(rr[3]+78);rr[5]=(rr[5]+4)&mask
            flags=cmpflags(rr[6],rr[0]);pc=0x26fa8 if signed(rr[6])<signed(rr[0]) else 0x27011;n+=5
            branches['loop' if pc==0x26fa8 else 'done']+=1
        elif mode==4:pc=restore();n=7
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        if flags is not None:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags/{i}')
    require(all(branches.values()),'missing branch coverage')
    return dict(cases=3072,cases_per_segment=512,segments=['first_line_and_opening_call','opening_guard','sound_block_call','loop','return','terminal_child_and_parent_loop'],branches=branches,all_registers=True,ordered_writes=True,mutable_memory_frame=True,modeled_flags=True,wrapping_stacks_and_counters=True,comparison='independent Python summary; universal proofs checked by Lean')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-noise-traversal.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-noise-traversal';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-noise-alert')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseTraversal'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original sound-line guards, recursive terminal calls and actual returns.')
if __name__=='__main__':main()

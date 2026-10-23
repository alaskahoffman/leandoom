#!/usr/bin/env python3
"""Certify original line opening and neighboring-sector selection."""
import argparse,json,random,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['opening_checked','neighbor_checked','machine_checked','line_checked']
NAMES+=['Doom.Proofs.NoiseOpening.'+n for n in ['decoded','entry_execution','closed_execution','ceiling_execution','floor_execution','range_execution','return_execution','neighbor_gate_execution','back_neighbor_execution','front_neighbor_execution']]
NAMES+=['Doom.Proofs.E1M1NoiseOpening.'+n for n in ['contains_opening','contains_prior','opening_execution','neighbor_execution','line_execution','block_execution']]
def certificate(raw):
    s='import Doom.Proofs.E1M1NoiseOpening\nset_option maxRecDepth 32768\nnamespace Doom.Verification.ExtractedNoiseOpening\nopen Doom Doom.Proofs X86 X86Memory X86Control\n'
    for name,b in raw.items():
        s+=f'def {name} : List UInt8 := ['+','.join(hex(v) for v in b)+f']\ntheorem {name}_checked : {name}=NoiseOpening.{name}Bytes := by decide\n'
    s+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (NoiseOpening.bytesProgram opening neighbor) [0x2c39f] 2 ⟨s,f,0x2c393⟩=some (NoiseOpening.range s) := by
  rw [opening_checked,neighbor_checked]; exact NoiseOpening.range_execution s f
 theorem line_checked (s : X86Memory.State) (f : Option Flags)
    (ret : (E1M1NoiseOpening.opened s f).pc=0x26fbb) :
    ∃ n, n≤55 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseOpening.program [] n ⟨s,f,0x26fb4⟩
      (E1M1NoiseOpening.blockResult s f) := E1M1NoiseOpening.block_execution s f ret
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseOpening\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseOpening.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw):
    """Independent diagnostic model; Lean supplies universal execution proofs."""
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2c340);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(CODE,0x40000);em.mem_map(0,0x30000);em.mem_map(0x500000,0x200000);em.mem_map(0xfffff000,4096)
    prior=json.loads((ROOT/'tests/reference/original-noise-traversal.json').read_text())
    em.mem_write(CODE+0x26fa6,bytes.fromhex(prior['units']['traversal']['hex']))
    em.mem_write(CODE+0x2c340,raw['opening']);em.mem_write(CODE+0x26fc4,raw['neighbor'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];stops=set()
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    sx16=lambda v:v if v<0x8000 else v-0x10000
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    branches={k:0 for k in ['one_sided','front_ceiling','back_ceiling','front_floor','back_floor','front_neighbor','back_neighbor','closed_gap','open_gap','blocked','ordinary','first_block','alias_opening','alias_neighbor']}
    for i in range(3072):
        mode=i//1024;j=i%1024
        line=HEAP+128+j%4;front=HEAP+512+j%4;back=HEAP+768+j%4;sidebase=HEAP+1536+j%4
        ix=[-32768,-1,0,1,32767];fi=ix[j%5];bi=ix[(j//5)%5]
        fslot=(sidebase+18*fi+14)&mask;bslot=(sidebase+18*bi+14)&mask
        addrs={0,0x2c000,HEAP,0xfffff000,fslot&~4095,(fslot+3)&~4095,bslot&~4095,(bslot+3)&~4095}
        pages={a:bytearray(rng.randbytes(4096)) for a in addrs}
        def put(a,v,n=4):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a,n=4):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=line;rr[2]=line
        rr[4]=[HEAP+3072+j%4,1,0xfffffff5][j%3];rr[1]=[0,1,0xffffffff][j%3]
        edges=[0,1,0x7fffffff,0x80000000,0xffffffff,rng.getrandbits(32)]
        # A ceiling output can alias the next floor input: honor write order.
        if mode==0 and j%7==0:front=0x2c034;branches['alias_opening']+=1
        put(line+22,fi,2);put(line+24,bi,2);put(line+46,front);put(line+50,back)
        put(front,edges[j%6]);put(front+4,edges[(j//6)%6]);put(back,edges[(j//36)%6]);put(back+4,edges[(j//216)%6])
        put(0x2c118,sidebase);put(fslot,front);put(bslot,back)
        rr[3]=get(fslot) if j%2 else HEAP+1000
        if mode==1 and j%7==0:
            rr[4]=fslot;rr[3]=sidebase if j%2 else HEAP+1000;branches['alias_neighbor']+=1
        flag=[0,64,68,4][(j//3)%4];put(line+16,flag,1)
        if mode==0:put(rr[4],CODE+0x28000)
        starts=[0x2c340,0x26fc4,0x26fb4];stops=[{0x28000},{0x26fee},{0x26f60,0x27006}][mode]
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        em.emu_start(CODE+starts[mode],CODE+0x40000,count=60)
        expected=[];n=0;flags=None
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        def push(v):rr[4]=(rr[4]-4)&mask;store(rr[4],v)
        def pop(r):rr[r]=get(rr[4]);rr[4]=(rr[4]+4)&mask
        if mode==2:rr[0]=rr[2];push(CODE+0x26fbb);n+=2
        if mode!=1:
            for r in [3,1,2,6]:push(rr[r])
            rr[2]=rr[0];rr[0]=sx16(get(rr[0]+24,2))&mask;n+=8
            if rr[0]==mask:
                rr[2]=0;flags=0x40;n+=2;branches['one_sided']+=1
            else:
                rr[0]=get(rr[2]+46);rr[2]=get(rr[2]+50);rr[3]=get(rr[0]+4);rr[1]=get(rr[2]+4);n+=6
                if signed(rr[3])>=signed(rr[1]):store(0x2c034,rr[1]);n+=1;branches['back_ceiling']+=1
                else:store(0x2c034,rr[3]);n+=2;branches['front_ceiling']+=1
                rr[3]=get(rr[0]);rr[6]=get(rr[2]);n+=4
                if signed(rr[3])<=signed(rr[6]):store(0x2c030,rr[6]);store(0x2c02c,rr[3]);n+=2;branches['back_floor']+=1
                else:store(0x2c030,rr[3]);store(0x2c02c,rr[6]);n+=3;branches['front_floor']+=1
                rr[2]=get(0x2c034);rr[2]=(rr[2]-get(0x2c030))&mask;n+=2
            store(0x2c038,rr[2])
            for r in [6,2,1,3]:pop(r)
            pc=get(rr[4])-CODE;rr[4]=(rr[4]+4)&mask;n+=6
            if mode==2:
                require(pc==0x26fbb,'actual opening return');gap=get(0x2c038);flags=cmpflags(gap,0);n+=2
                pc=0x26fc4 if signed(gap)>0 else 0x27006;branches['open_gap' if signed(gap)>0 else 'closed_gap']+=1
        if mode==1 or (mode==2 and pc==0x26fc4):
            rr[0]=sx16(get(rr[2]+22,2))&mask;rr[0]=(rr[0]*18)&mask;rr[7]=get(0x2c118);rr[0]=(rr[0]+rr[7])&mask
            store(rr[4],rr[7]);rr[7]=get(rr[0]+14);flags=cmpflags(rr[3],rr[7]);n+=8
            if rr[3]==rr[7]:
                rr[0]=sx16(get(rr[2]+24,2))&mask;rr[0]=(rr[0]*18)&mask;rr[0]=(rr[0]+get(rr[4]))&mask;rr[0]=get(rr[0]+14);flags=None;n+=5;branches['back_neighbor']+=1
            else:rr[0]=rr[7];n+=1;branches['front_neighbor']+=1
            pc=0x26fee
            if mode==2:
                block=get(rr[2]+16,1)&64
                if not block:rr[2]=rr[1];flags=0x40;push(CODE+0x27006);pc=0x26f60;n+=4;branches['ordinary']+=1
                elif rr[1]==0:rr[2]=1;flags=0x40;push(CODE+0x27006);pc=0x26f60;n+=7;branches['first_block']+=1
                else:flags=(int(rr[1]==0)<<6)|((rr[1]>>31)<<7);pc=0x27006;n+=4;branches['blocked']+=1
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        if flags is not None:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags/{i}')
    require(all(branches.values()),'missing branch coverage')
    return dict(cases=3072,opening_cases=1024,neighbor_cases=1024,joined_cases=1024,branches=branches,all_registers=True,ordered_writes=True,mutable_memory_frame=True,modeled_flags=True,wrapping_stacks=True,signed_height_and_side_boundaries=True,aliased_reads=True,comparison='independent Python summary; universal proofs checked by Lean')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-noise-opening.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-noise-opening';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-noise-traversal')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseOpening'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original opening calculation, neighbor selection and joined sound-line call.')
if __name__=='__main__':main()

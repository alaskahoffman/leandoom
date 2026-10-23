#!/usr/bin/env python3
"""Certify original noise-alert setup, sector guard/writes and firing composition."""
import argparse,json,random,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['entry_checked','sector_checked','machine_checked','fire_checked']
NAMES+=['Doom.Proofs.NoiseAlert.'+n for n in ['decoded','entry_execution','result_target','result_count','result_frame','prepare_execution','gate_execution','update_execution','update_frame','updated_target','updated_cost','updated_stamp']]
NAMES+=['Doom.Proofs.E1M1NoiseAlert.'+n for n in ['contains_noise','contains_prior','sector_execution','alert_execution','fire_execution']]
def certificate(raw):
    s='import Doom.Proofs.E1M1NoiseAlert\nset_option maxRecDepth 32768\nnamespace Doom.Verification.ExtractedNoiseAlert\nopen Doom Doom.Proofs X86 X86Memory X86Control\n'
    for name,b in raw.items():
        s+=f'def {name} : List UInt8 := ['+','.join(hex(v) for v in b)+f']\ntheorem {name}_checked : {name}=NoiseAlert.{name}Bytes := by decide\n'
    s+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (NoiseAlert.bytesProgram entry sector) [0x26f60] 8 ⟨s,f,0x27020⟩=some (NoiseAlert.result s) := by
  rw [entry_checked,sector_checked]; exact NoiseAlert.entry_execution s f
 theorem fire_checked (s : X86Memory.State) (f : Option Flags) (enough : E1M1WeaponFire.Enough s)
    (actor : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (attack : E1M1WeaponContinuation.AttackReturns s) :
    ∃ n, n≤141 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseAlert.program [] n ⟨s,f,0x2d410⟩
      (E1M1NoiseAlert.result (E1M1NoiseAlert.noiseCall s).core) := E1M1NoiseAlert.fire_execution s f enough actor attack
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseAlert\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseAlert.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def cross_check(raw):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x27020);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(CODE,0x40000);em.mem_map(0,0x30000);em.mem_map(HEAP,4096);em.mem_map(0xfffff000,4096)
    em.mem_write(CODE+0x27020,raw['entry']);em.mem_write(CODE+0x26f60,raw['sector'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];stops=set()
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    branches=dict(fresh=0,better_route=0,pruned=0,positive_lines=0,nonpositive_lines=0)
    for i in range(2048):
        mode=0 if i<512 else 1 if i<1536 else 2
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,0x13000,0x2b000,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate((v&mask).to_bytes(4,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(4)),'little')
        rr=[rng.getrandbits(32) for _ in regs];sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        rr[4]=sp;sec=HEAP+512+i%4;emitter=HEAP+128+i%4;sub=HEAP+256+i%4;target=HEAP+1024
        counter=[0,1,0x7fffffff,0xffffffff,rng.getrandbits(32)][i%5]
        blocks=[0,1,0x7fffffff,0xffffffff,rng.getrandbits(32)][(i//5)%5]
        linecount=[0,1,4,0x80000000,0xffffffff][i%5]
        put(0x13580,counter);put(0x2b958,target);put(sec+78,linecount)
        stamp=counter if mode==1 else (counter+1)&mask
        put(sec+66,stamp if i%3 else (stamp-1)&mask)
        cost=(blocks+1)&mask if mode==1 else 1
        put(sec+18,[cost,(cost+1)&mask,(cost-1)&mask][i%3])
        if mode==1:rr[0]=sec;rr[2]=blocks;start=0x26f60
        else:
            rr[0]=target;rr[2]=emitter;put(emitter+52,sub);put(sub,sec);start=0x27020
            if mode==0 and i%7==0:
                # The target store changes the subsector read: intentional alias.
                put(emitter+52,0x2b958)
        stops={0x26f60} if mode==0 else {0x26fa6,0x27011}
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        em.emu_start(CODE+start,CODE+0x40000,count=33)
        expected=[];n=0
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        if mode!=1:
            store(0x2b958,rr[0]);rr[0]=get(rr[2]+52);rr[2]=(get(0x13580)+1)&mask
            rr[0]=get(rr[0]);store(0x13580,rr[2]);rr[2]=0;flags=0x40;n=8;pc=0x26f60
        if mode!=0:
            for r in [3,1,6,7,5]:rr[4]=(rr[4]-4)&mask;store(rr[4],rr[r])
            rr[4]=(rr[4]-4)&mask;rr[3]=rr[0];rr[1]=rr[2];rr[2]=get(0x13580);n+=11
            old=get(rr[0]+66);flags=cmpflags(rr[2],old);update=True
            if rr[2]==old:
                rr[0]=(rr[1]+1)&mask;oldcost=get(rr[3]+18);flags=cmpflags(rr[0],oldcost);n+=3
                if signed(rr[0])>=signed(oldcost):update=False;branches['pruned']+=1
                else:branches['better_route']+=1
            else:branches['fresh']+=1
            if update:
                rr[0]=get(0x13580);store(rr[3]+66,rr[0]);rr[0]=(rr[1]+1)&mask;rr[7]=get(rr[3]+78)
                store(rr[3]+18,rr[0]);rr[0]=get(0x2b958);rr[6]=0;store(rr[3]+22,rr[0]);n+=10
                flags=(int(rr[7]==0)<<6)|((rr[7]>>31)<<7);pc=0x27011 if signed(rr[7])<=0 else 0x26fa6
                branches['positive_lines' if signed(rr[7])>0 else 'nonpositive_lines']+=1
            else:pc=0x27011
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags/{i}')
    require(all(branches.values()),'missing branch coverage')
    return dict(entry_cases=512,sector_cases=1024,joined_alert_cases=512,branches=branches,all_registers=True,ordered_writes=True,mutable_memory_frame=True,modeled_flags=True,wrapping_counters_and_stacks=True,aliased_entry_reads=True)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-noise-alert.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-noise-alert';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-rejection')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseAlert'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original noise entry, sector guard/writes and firing composition.')
if __name__=='__main__':main()

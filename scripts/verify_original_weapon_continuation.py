#!/usr/bin/env python3
"""Certify supported fallback selection and the real attack-state/noise continuation."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
import verify_original_weapon_fire as fire
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','state5_checked','state13_checked','state21_checked','machine_checked','live_checked','empty_checked','noise_checked','rejected_checked']
NAMES+=['Doom.Proofs.WeaponFallback.'+n for n in ['decoded','prepare_execution','choose_execution','prepared_inventory','chosen_pending','selected_not_sentinel','call_execution','retry_execution','execution','return_execution','live_choice','lowered_pending','result_pending','call_live']]
NAMES+=['Doom.Proofs.E1M1WeaponContinuation.'+n for n in ['attack_tables','contains_fallback','contains_prior','empty_execution','setter_return_execution','attack_return_execution','noise_execution','rejected_return_execution']]

def table_data(binary,profile,spec):
    le=int(profile['le_offset'],16);u32=lambda p:struct.unpack_from('<I',binary,p)[0]
    require(struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)==(0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    require([r['index'] for r in spec['states']]==[5,13,21],'wrong state indices')
    result={}
    for row in spec['states']:
        index=row['index'];start=0x15a28+28*index;raw=bytearray()
        require(int(row['offset'],16)==start,'wrong state offset')
        for a in range(start,start+28):
            at=le+u32(le+0x48)+4*(70+a//4096)
            require(binary[at+3]==0,'unsupported table page');physical=int.from_bytes(binary[at:at+3],'big')
            require(physical>0,'unmapped table page');off=int(profile['data_pages_offset'],16)+(physical-1)*4096+a%4096
            require(off<len(binary),'truncated table page');raw.append(binary[off])
        require(raw.hex()==row['hex'],'state bytes differ')
        relocs=extraction.fixups(binary,range(70+start//4096,70+(start+27)//4096+1))
        require(not any(max(70*4096+start,p)<min(70*4096+start+28,p+4) for p,_,_ in relocs),'unexpected state relocation')
        result[index]=bytes(raw)
    return result

def certificate(raw,states):
    s='import Doom.Proofs.E1M1WeaponContinuation\nset_option maxRecDepth 32768\nnamespace Doom.Verification.ExtractedWeaponContinuation\nopen Doom Doom.Proofs X86 X86Memory X86Control\n'
    s+='def extracted : List UInt8 := ['+','.join(hex(v) for v in raw)+']\ntheorem bytes_checked : extracted=WeaponFallback.code := by decide\n'
    for index,b in states.items():
        s+=f'def state{index} : List UInt8 := ['+','.join(hex(v) for v in b)+f']\ntheorem state{index}_checked : state{index}=E1M1WeaponContinuation.state{index} := by decide\n'
    s+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags) (h : WeaponFallback.Inventory s) :
    ∃ n, n≤32 ∧ X86Routine.Prefix (WeaponFallback.bytesProgram extracted) [] n ⟨s,f,0x2d19f⟩ (WeaponFallback.result s) := by
  rw [bytes_checked]; exact WeaponFallback.execution s f h
 theorem live_checked (s : X86Memory.State) (own : Bool) (sh bu : Int32) (h : WeaponFallback.Inputs s own sh bu) :
    WeaponFallback.selected s=BitVec.ofNat 32 (Weapon.fallbackWeapon own sh bu).val := WeaponFallback.live_choice s own sh bu h
 theorem empty_checked (s : X86Memory.State) (f : Option Flags) (empty : ¬E1M1WeaponFire.Enough s)
    (inventory : WeaponFallback.Inventory (E1M1WeaponFire.afterCheck s).core) :
    ∃ n, n≤62 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponContinuation.program [] n ⟨s,f,0x2d410⟩
      (WeaponFallback.result (E1M1WeaponFire.afterCheck s).core) := E1M1WeaponContinuation.empty_execution s f empty inventory
 theorem noise_checked (s : X86Memory.State) (f : Option Flags) (h : E1M1WeaponFire.Enough s)
    (setter : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a)
    (ret : E1M1WeaponContinuation.AttackReturns s) :
    ∃ n, n≤109 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponContinuation.program [] n ⟨s,f,0x2d410⟩
      (WeaponFire.noiseCall (E1M1WeaponContinuation.attackReturn s).core (E1M1WeaponContinuation.attackReturn s).flags) :=
  E1M1WeaponContinuation.noise_execution s f h setter ret
 theorem rejected_checked (s : X86Memory.State) (f : Option Flags) (ret : (WeaponFallback.returned s).pc=0x2d41a) :
    ∃ n, n≤12 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponContinuation.program [] n ⟨s,f,0x2d2aa⟩
      (WeaponFire.returned (WeaponFallback.returned s).core (some (logical32 0))) :=
  E1M1WeaponContinuation.rejected_return_execution s f ret
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponContinuation\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponContinuation.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,states,prior,data,actor,setter):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d19f);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(CODE,0x40000),(0,0x30000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    for pc,b in [(0x2d19f,raw),(0x30ea0,actor),(0x2d040,setter)]+[(pc,prior[name]) for name,pc in [('entry',0x2d460),('decision',0x2d176),('fire',0x2d410)]]:em.mem_write(CODE+pc,b)
    em.mem_write(0x16b00,data['pose']);em.mem_write(0x12d90,data['weapons'])
    for index,b in states.items():em.mem_write(0x15a28+28*index,b)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];stop=0
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a==stop:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    choices={0:0,1:0,2:0}
    for i in range(2304):
        mode=0 if i<1024 else 1 if i<2048 else 2
        p=HEAP+64+i%4;obj=HEAP+1024+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&mask)):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=p;rr[4]=sp;original=rr.copy()
        w=i%3;put(p,obj);put(p+112,w)
        saved=[rng.getrandbits(32) for _ in range(9)]
        own=[0,1,2][i%3];sh=[0,1,0xffffffff,0x80000000,0x7fffffff][i%5];bu=[0,1,0xffffffff,0x7fffffff][(i//5)%4]
        if mode==0:
            for off in [132,136,140,144,148,152]:put(p+off,0)
            put(p+128,own);put(p+160,sh);put(p+156,bu)
            start=0x2d19f;stop=CODE+0x2d040
        elif mode==1:
            put(p+156,1+i%50);put(p+160,1+i%8)
            start=0x2d410;stop=CODE+0x27020
        else:
            saved[4]=CODE+0x2d41a;saved[8]=CODE+0x2d38d
            for k,v in enumerate(saved):put(sp+4*k,v)
            start=0x2d2aa;stop=CODE+0x2d38d
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        em.emu_start(CODE+start,CODE+0x40000,count=120)
        expected=[]
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        if mode==0:
            selected=2 if own and sh else 1 if bu else 0;choices[selected]+=1
            store(p+116,selected);store(sp-4,CODE+0x2d2aa)
            rr[2]=0;rr[3]=[3,11,19][w];rr[4]=(sp-4)&mask
            if selected!=2:rr[1]=bu
            if selected==0:rr[6]=0
            n=22 if selected==2 else (23 if own==0 else 25) if selected==1 else (29 if own==0 else 31)
        elif mode==1:
            for k,r in enumerate([3,1,2],1):store(sp-4*k,original[r])
            store(sp-16,CODE+0x2d41a)
            for k,v in enumerate([original[3],p,original[2],original[6]],1):store(sp-16-4*k,v)
            store(sp-16,CODE+0x2d42a);store(sp-20,original[3]);store(sp-24,original[6])
            for off,value in [(100,0x16b00),(96,12),(36,28),(40,4)]:store(obj+off,value)
            store(sp-16,CODE+0x2d446);store(sp-20,p);store(sp-24,original[6])
            store(p+244,0x15a28+28*[5,13,21][w]);store(p+248,[4,4,3][w]);store(sp-16,CODE+0x2d44f)
            rr[0]=obj;rr[1]=p;rr[2]=obj;rr[3]=p+244;rr[4]=(sp-16)&mask;n=94 if w==0 else 96
        else:
            rr[0]=0;rr[6]=saved[0];rr[2]=saved[5];rr[1]=saved[6];rr[3]=saved[7];rr[4]=(sp+36)&mask;n=12
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==stop and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==(0 if mode==1 else 0x40),f'flags/{i}')
    return dict(fallback_cases=1024,attack_through_noise_call_cases=1024,rejection_double_return_cases=256,selections=choices,all_registers=True,ordered_writes=True,mutable_memory_frame=True,flags=True,unaligned_and_wrapping_stacks=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-weapon-continuation.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    def extract(name):return extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/name).read_text()))
    raw=extraction.extract(binary,profile,spec)['fallback'];states=table_data(binary,profile,spec)
    prior=extract('original-weapon-fire.json');data=fire.table_data(binary,profile,json.loads((ROOT/'tests/reference/original-weapon-fire.json').read_text()))
    actor=extract('original-player-animation.json')['setMobjStateBytes'];setter=extract('original-weapon-drop.json')['setter']
    out=ROOT/'artifacts/original-weapon-continuation';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-fire')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponContinuation'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,states));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,states,prior,data,actor,setter) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: supported fallback, attack-state return, noise call and rejected firing return.')
if __name__=='__main__':main()

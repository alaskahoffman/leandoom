#!/usr/bin/env python3
"""Certify in-progress lowering and the joined rejected-shot execution."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
import verify_original_weapon_fire as fire
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','state3_checked','state11_checked','state19_checked','machine_checked','joined_checked']
NAMES+=['Doom.Proofs.WeaponLowerProgress.'+n for n in ['execution','advanced_height','below_height','return_address','live_height','registers','live_correspondence']]
NAMES+=['Doom.Proofs.E1M1WeaponRejection.'+n for n in ['lower_tables','contains_ready','contains_setter','contains_lower','lower_return_execution','rejected_execution']]

def table_data(binary,profile,spec):
    le=int(profile['le_offset'],16);u32=lambda p:struct.unpack_from('<I',binary,p)[0]
    require(struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)==(0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    require([r['index'] for r in spec['states']]==[3,11,19],'wrong state indices')
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
        relocs=[dict(offset=p-(70*4096+start),object=o,target=hex(t)) for p,o,t in relocs if max(70*4096+start,p)<min(70*4096+start+28,p+4)]
        require(relocs==row['relocations']==[dict(offset=12,object=1,target='0x2d490')],'wrong action relocation')
        # Code-object-relative address space used by the Lean machine model.
        struct.pack_into('<I',raw,12,0x2d490)
        result[index]=bytes(raw)
    return result

def certificate(raw,states):
    s='import Doom.Proofs.E1M1WeaponRejection\nset_option maxRecDepth 32768\nnamespace Doom.Verification.ExtractedWeaponRejection\nopen Doom Doom.Proofs X86 X86Memory X86Control\n'
    s+='def extracted : List UInt8 := ['+','.join(hex(v) for v in raw)+']\ntheorem bytes_checked : extracted=WeaponLower.code := by decide\n'
    for index,b in states.items():
        s+=f'def state{index} : List UInt8 := ['+','.join(hex(v) for v in b)+f']\ntheorem state{index}_checked : state{index}=E1M1WeaponRejection.state{index} := by decide\n'
    s+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags)
    (low : WeaponLower.below s) (ret : load32 (WeaponLower.advancedMemory s) (s.regs 4)=0x2d095) :
    X86Routine.run (WeaponLower.bytesProgram extracted) [0x2d095] 6 ⟨s,f,0x2d490⟩=some (WeaponLower.result s) := by
  rw [bytes_checked]; exact WeaponLowerProgress.execution s f low ret
 theorem joined_checked (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (empty : ¬E1M1WeaponFire.Enough s)
    (inventory : WeaponFallback.Inventory (E1M1WeaponFire.afterCheck s).core)
    (lower : E1M1WeaponRejection.LowerReturns (E1M1WeaponRejection.fallback s).core t)
    (setterPC : t.pc=0x2d2aa) (ammoPC : (WeaponFallback.returned t.core).pc=0x2d41a) :
    ∃ n, n≤122 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponRejection.program [] n ⟨s,f,0x2d410⟩
      (E1M1WeaponRejection.rejected t) := E1M1WeaponRejection.rejected_execution s f t empty inventory lower setterPC ammoPC
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponRejection\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponRejection.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,states,prior,fallback,setter,weapons):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d4cb);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(CODE,0x40000),(0,0x30000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    for pc,b in [(0x2d490,raw),(0x2d19f,fallback),(0x2d040,setter)]+[(pc,prior[name]) for name,pc in [('entry',0x2d460),('decision',0x2d176),('fire',0x2d410)]]:em.mem_write(CODE+pc,b)
    em.mem_write(0x12d90,weapons)
    for index,b in states.items():
        b=bytearray(b);struct.pack_into('<I',b,12,CODE+0x2d490);em.mem_write(0x15a28+28*index,bytes(b))
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];stop=0
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(n*8))-1))))
    def visit(e,a,_n,_d):
        if a==stop:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    selections={0:0,1:0,2:0}
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    for i in range(1536):
        whole=i<1024;p=HEAP+64+i%4;psp=p+244;sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v,size=4):
            for k,b in enumerate((v&((1<<(8*size))-1)).to_bytes(size,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=p;rr[4]=sp
        y=[0,0x200000,0x79ffff,0x7fffffff,0x80000000,0xffffffff][i%6] if i%2 else rng.getrandbits(32)
        while signed((y+0x60000)&mask)>=0x800000:y=rng.getrandbits(32)
        advanced=(y+0x60000)&mask;put(psp+12,y);put(p+4,i%3);put(p+32,rng.getrandbits(32))
        w=1+i%2;own=i%3!=0;sh=(i%8)+1 if w==1 and i%4 else 0;bu=(i%50)+1 if w==2 and i%4 else 0
        if whole:
            for off in [132,136,140,144,148,152]:put(p+off,0)
            put(p+112,w);put(p+128,int(own));put(p+160,sh);put(p+156,bu);put(sp,CODE+0x2d38d)
            start=0x2d410;stop=CODE+0x2d38d
        else:
            rr[2]=psp;put(sp,CODE+0x2d095);start=0x2d490;stop=CODE+0x2d095
        original=rr.copy()
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        em.emu_start(CODE+start,CODE+0x40000,count=123)
        expected=[]
        def store(a,v,size=4):expected.append((a&mask,size,v&((1<<(8*size))-1)));put(a,v,size)
        if whole:
            selected=2 if own and sh else 1 if bu else 0;selections[selected]+=1
            for k,r in enumerate([3,1,2],1):store(sp-4*k,original[r])
            store(sp-16,CODE+0x2d41a)
            for k,v in enumerate([original[3],p,original[2],original[6]],1):store(sp-16-4*k,v)
            store(p+116,selected);store(sp-36,CODE+0x2d2aa)
            store(sp-40,p if selected==2 else bu);store(sp-44,0 if selected==0 else original[6])
            store(psp,0x15a28+28*[3,11,19][w]);store(psp+4,1)
            store(sp-48,CODE+0x2d095);store(sp-52,psp);store(psp+14,advanced>>16,2)
            rr[0]=0;rr[4]=(sp+4)&mask
            fallback_n=22 if selected==2 else (23 if not own else 25) if selected==1 else (29 if not own else 31)
            n=74+fallback_n;flags=0x40
            require(0x27020 not in visits and 0x30ea0 not in visits,'rejected shot entered attack/noise')
        else:
            store(sp-4,rr[3]);store(psp+14,advanced>>16,2);rr[4]=(sp+4)&mask;n=6
            diff=(advanced-0x800000)&mask
            flags=(int(advanced<0x800000))|(int(diff==0)<<6)|((diff>>31)<<7)|(int(bool((advanced^0x800000)&(advanced^diff)&0x80000000))<<11)
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==stop and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,f'flags/{i}')
    return dict(whole_rejection_cases=1024,lower_callback_cases=512,selections=selections,all_registers=True,ordered_writes=True,mutable_memory_frame=True,modeled_flags=True,unaligned_and_wrapping_stacks=True,signed_height_edges=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-weapon-rejection.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    def extract(name):return extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/name).read_text()))
    raw=extract('original-weapon-lower.json')['lower'];states=table_data(binary,profile,spec)
    prior=extract('original-weapon-fire.json');data=fire.table_data(binary,profile,json.loads((ROOT/'tests/reference/original-weapon-fire.json').read_text()))
    fallback=extract('original-weapon-continuation.json')['fallback'];setter=extract('original-weapon-drop.json')['setter']
    out=ROOT/'artifacts/original-weapon-rejection';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-continuation')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponRejection'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,states));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,states,prior,fallback,setter,data['weapons']) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: in-progress lowering and joined rejected-shot execution.')
if __name__=='__main__':main()

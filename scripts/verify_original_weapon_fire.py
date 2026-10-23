#!/usr/bin/env python3
"""Certify DOS ammo acceptance, real returns, and attack-pose dispatch."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['entry_checked','decision_checked','fire_checked','pose_checked','weapons_checked','machine_checked','live_checked','joined_checked','ready_checked']
NAMES+=['Doom.Proofs.WeaponAmmo.'+n for n in ['decoded','prepare_execution','cost_execution','decision_execution','return_execution','check_execution','execution','live_decision','success_return']]
NAMES+=['Doom.Proofs.WeaponFire.'+n for n in ['decoded','check_call_execution','branch_execution','pose_call_execution','attack_call_execution','noise_call_execution','return_execution','attack_live']]
NAMES+=['Doom.Proofs.E1M1WeaponFire.'+n for n in ['table_decoded','weapon_table','contains_ammo','contains_fire','contains_prior','check_execution','check_return','pose_call_execution','pose_execution','live_pose','attack_execution','attack_state_execution','ready_fire_execution']]

def table_data(binary,profile,spec):
    le=int(profile['le_offset'],16);u32=lambda p:struct.unpack_from('<I',binary,p)[0]
    require(struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)==(0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    result={}
    for name,start,size in [('pose',0x16b00,28),('weapons',0x12d90,72)]:
        row=spec['data'][name];require(int(row['offset'],16)==start,'wrong table offset');raw=bytearray()
        for a in range(start,start+size):
            at=le+u32(le+0x48)+4*(70+a//4096)
            require(binary[at+3]==0,'unsupported table page');physical=int.from_bytes(binary[at:at+3],'big')
            require(physical>0,'unmapped table page')
            offset=int(profile['data_pages_offset'],16)+(physical-1)*4096+a%4096
            require(offset<len(binary),'truncated table page');raw.append(binary[offset])
        require(raw.hex()==row['hex'],'table bytes differ: '+name)
        relocs=extraction.fixups(binary,range(70+start//4096,70+(start+size-1)//4096+1))
        require(not any(max(70*4096+start,p)<min(70*4096+start+size,p+4) for p,_,_ in relocs),'unexpected table relocation')
        result[name]=bytes(raw)
    return result

def certificate(raw,data):
    s='import Doom.Proofs.E1M1WeaponFire\nnamespace Doom.Verification.ExtractedWeaponFire\nopen Doom Doom.Proofs X86 X86Memory X86Control\n'
    targets={'entry':'WeaponAmmo.entryBytes','decision':'WeaponAmmo.decisionBytes','fire':'WeaponFire.code','pose':'E1M1WeaponFire.poseBytes','weapons':'E1M1WeaponFire.weaponsBytes'}
    for name,b in {**raw,**data}.items():
        s+='def '+name+' : List UInt8 := ['+','.join(hex(v) for v in b)+']\n'
        s+='theorem '+name+'_checked : '+name+'='+targets[name]+' := by decide\n'
    s+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤25 ∧ X86Routine.Prefix (WeaponAmmo.bytesProgram entry decision) [] n ⟨s,f,0x2d460⟩ (WeaponAmmo.result s) := by
  rw [entry_checked,decision_checked]; exact WeaponAmmo.execution s f
 theorem live_checked (s : X86Memory.State) (w : Fin 3) (ammo : Int32) (h : WeaponAmmo.Inputs s w ammo) :
    (WeaponAmmo.checked s).pc=(if Weapon.ammoAvailable w.val ammo then 0x2d195 else 0x2d19f) :=
  WeaponAmmo.live_decision s w ammo h
 theorem joined_checked (s : X86Memory.State) (f : Option Flags) (h : E1M1WeaponFire.Enough s)
    (setter : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall s).core 0x2d42a) :
    ∃ n, n≤66 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponFire.program [] n ⟨s,f,0x2d410⟩
      (WeaponFire.attackCall (E1M1WeaponFire.afterPose s).core) := E1M1WeaponFire.attack_execution s f h setter
'''
    s+='''theorem ready_checked (s : X86Memory.State) (f : Option Flags)
    (fire : (WeaponReadyGate.result s).pc=0x2d410)
    (h : E1M1WeaponFire.Enough (WeaponReadyGate.result s).core)
    (setter : DeathSetter.SetterInputs E1M1WeaponFire.entry (E1M1WeaponFire.poseCall (WeaponReadyGate.result s).core).core 0x2d42a) :
    ∃ n, n≤111 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponFire.program [] n ⟨s,f,0x2d333⟩
      (E1M1PspriteSetter.setterResult (WeaponFire.attackCall (E1M1WeaponFire.afterPose (WeaponReadyGate.result s).core).core).core) :=
  E1M1WeaponFire.ready_fire_execution s f fire h setter
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponFire\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponFire.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,data,setter):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d410);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(CODE,0x40000),(0,0x30000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    for name,pc in [('entry',0x2d460),('decision',0x2d176),('fire',0x2d410)]:em.mem_write(CODE+pc,raw[name])
    em.mem_write(CODE+0x30ea0,setter);em.mem_write(0x16b00,data['pose']);em.mem_write(0x12d90,data['weapons'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];stops=set()
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    passed=failed=0
    for i in range(2048):
        full=i>=1024;w=i%3;ammo=[0,1,0xffffffff,0x80000000,0x7fffffff,2,rng.getrandbits(32)][i%7]
        signed=ammo if ammo<2**31 else ammo-2**32;allowed=w==0 or signed>0
        p=HEAP+64+i%4;obj=HEAP+1024+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        ret=CODE+0x28000
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&mask)):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        put(p,obj);put(p+112,w);put(p+156+(4 if w==2 else 0),ammo);put(sp,ret)
        for a,b in pages.items():em.mem_write(a,bytes(b))
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=p;rr[4]=sp;original=rr.copy()
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        stops={CODE+0x2d19f,CODE+0x2d040} if full else {CODE+0x2d19f,ret}
        em.emu_start(CODE+(0x2d410 if full else 0x2d460),CODE+0x40000,count=80)
        expected=[]
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        if full:
            for k,r in enumerate([3,1,2],1):store(sp-4*k,rr[r])
            store(sp-16,CODE+0x2d41a);rr[1]=p;ammo_sp=(sp-16)&mask
        else:ammo_sp=sp
        for k,r in enumerate([3,1,2,6],1):store(ammo_sp-4*k,rr[r])
        if not allowed:
            rr[2]=1;rr[3]=1 if w==2 else 0;rr[4]=(ammo_sp-16)&mask
            pc=CODE+0x2d19f;n=18+(5 if full else 0);failed+=1
        elif not full:
            rr[0]=1;rr[4]=(sp+4)&mask;pc=ret;n=22 if w==0 else 24;passed+=1
        else:
            store(sp-16,CODE+0x2d42a);store(sp-20,original[3]);store(sp-24,original[6])
            for off,value in [(100,0x16b00),(96,12),(36,28),(40,4)]:store(obj+off,value)
            store(sp-16,CODE+0x2d446)
            rr[0]=p;rr[1]=p;rr[2]=0;rr[3]=[5,13,21][w];rr[4]=(sp-16)&mask
            pc=CODE+0x2d040;n=63 if w==0 else 65;passed+=1
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,f'attack flags/{i}')
        require(writes==expected,f'ordered writes/{i}: {writes} != {expected}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==pc and len(visits)==n,f'endpoint/count/{i}: {len(visits)} != {n}')
    return dict(ammo_cases=1024,fire_through_pose_cases=1024,accepted=passed,insufficient=failed,all_registers=True,ordered_writes=True,mutable_memory_frame=True,unaligned_and_wrapping_stacks=True,signed_ammo_boundaries=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text());spec=json.loads((ROOT/'tests/reference/original-weapon-fire.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec);data=table_data(binary,profile,spec)
    setter=extraction.extract(binary,profile,json.loads((ROOT/'tests/reference/original-player-animation.json').read_text()))['setMobjStateBytes']
    out=ROOT/'artifacts/original-weapon-fire';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-ready-reset')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponFire'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,data));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,data,setter) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: ammo acceptance, actual return, attack pose and state dispatch.')
if __name__=='__main__':main()

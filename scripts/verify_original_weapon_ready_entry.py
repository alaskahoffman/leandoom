#!/usr/bin/env python3
"""Certify the ready entry, pose/sound gates, and uninterrupted idle joins."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
import verify_original_thrust as thrust
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','machine_checked','pose_checked','joined_checked','raising_checked']
NAMES+=['Doom.Proofs.WeaponReadyEntry.'+n for n in ['decoded','prologue','branch_execution','reset_execution','sound_execution','execution','pose_decision','no_chainsaw','ready_boundary','reset_arguments']]
NAMES+=['Doom.Proofs.E1M1WeaponReadyEntry.'+n for n in ['contains_entry','contains_prior','entry_to_gate','decision_execution','idle_execution','nested_execution','raise_idle_return','idle_live']]

def certificate(raw):
    return '''import Doom.Proofs.E1M1WeaponReadyEntry
namespace Doom.Verification.ExtractedWeaponReadyEntry
open Doom Doom.Proofs X86 X86Memory X86Control
 def extracted : List UInt8 := ['''+','.join(hex(b) for b in raw)+''']
 theorem bytes_checked : extracted=WeaponReadyEntry.code := by decide
 theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤19 ∧ X86Routine.Prefix (WeaponReadyEntry.bytesProgram extracted) [] n ⟨s,f,0x2d2f0⟩ (WeaponReadyEntry.result s) := by
  rw [bytes_checked]; exact WeaponReadyEntry.execution s f
 theorem pose_checked (s : X86Memory.State) (frame : Fin 967) (w : Fin 3)
    (h : WeaponReadyEntry.Inputs s frame w) :
    WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s) ↔ frame.val=154 ∨ frame.val=155 :=
  WeaponReadyEntry.pose_decision s frame w h
 theorem joined_checked (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (h : WeaponReadyEntry.Inputs s frame w) (idlePose : frame.val≠154 ∧ frame.val≠155)
    (low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared s))
    (a : WeaponReadyGate.attack (WeaponReadyEntry.prepared s)=0) :
    ∃ n, n≤58 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyEntry.program [] n ⟨s,f,0x2d2f0⟩ (WeaponReady.result (WeaponReadyEntry.prepared s)) :=
  E1M1WeaponReadyEntry.idle_execution s f frame w h idlePose low a
 theorem raising_checked (s : X86Memory.State) (f : Option Flags) (frame : Fin 967) (w : Fin 3)
    (ready : (E1M1WeaponReady.raiseNext s).pc=0x2d2f0)
    (h : WeaponReadyEntry.Inputs (E1M1WeaponReady.raiseNext s).core frame w)
    (idlePose : frame.val≠154 ∧ frame.val≠155)
    (low : ¬WeaponReadyGate.lowering (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core))
    (a : WeaponReadyGate.attack (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core)=0)
    (t : X86Control.State)
    (ok : E1M1WeaponReady.raisedIdleReturn (WeaponReadyEntry.prepared (E1M1WeaponReady.raiseNext s).core)=some t) :
    ∃ n, n≤133 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyEntry.program [] n ⟨s,f,0x2d4d0⟩ t :=
  E1M1WeaponReadyEntry.raise_idle_return s f frame w ready h idlePose low a t ok
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponReadyEntry\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponReadyEntry.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,gate,idle,table):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d2f0);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(CODE,0x40000),(0,0x30000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    em.mem_write(CODE+0x2d2f0,raw+gate+idle)
    em.mem_write(0x5a84,table);em.mem_write(0x13584,struct.pack('<I',0x7a84))
    trig=struct.unpack('<10240i',table);signed=lambda v:v if v<2**31 else v-2**32
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    exits={0x2d333,0x30ea0,0x3f370};writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE in exits:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    cases=[(0x15a28+28*f,w,0x1617c) for f in range(967) for w in [0,1,2]]
    cases += [(p,w,ps) for p in [0,0x16b00,0x16b1c,0xffffffff] for w in [0,1,2,7,0xffffffff] for ps in [0,0x1617c,0xffffffff]]
    cases += [(rng.choice([0x16b00,0x16b1c,rng.getrandbits(32)]),rng.choice([7,rng.getrandbits(32)]),rng.choice([0x1617c,rng.getrandbits(32)])) for _ in range(4096)]
    entry_count=len(cases);cases += [(0x16a74,1,0x15b40)]*512
    counts={0x2d333:0,0x30ea0:0,0x3f370:0,0x2d095:0}
    for i,(pose,w,ps) in enumerate(cases):
        full=i>=entry_count
        exits={0x2d095} if full else {0x2d333,0x30ea0,0x3f370}
        p=HEAP+64+i%4;obj=HEAP+1024+i%4;slot=HEAP+512+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        elif not full and i%17==0:sp=p+128 # saved registers overlap weapon field
        elif not full and i%19==0:sp=obj+116 # saved registers overlap pose pointer
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&mask)):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a):return sum(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095]<<(8*k) for k in range(4))
        put(p,obj);put(obj+100,pose);put(p+112,w);put(slot,ps)
        amplitude,time=rng.getrandbits(32),rng.getrandbits(32)
        if full:
            put(p+116,10);put(p+32,100);put(p+28,amplitude);put(sp,CODE+0x2d095)
            pages[HEAP][p+15-HEAP]=0
        for a,data in pages.items():em.mem_write(a,bytes(data))
        em.mem_write(0x2cf80,struct.pack('<I',time))
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=p;rr[2]=slot;rr[4]=sp;original=rr.copy()
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        em.emu_start(CODE+0x2d2f0,CODE+0x40000,count=60)
        expected=[]
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        for k,r in enumerate([3,1,6,7],1):store(sp-4*k,rr[r])
        rr[4]=(sp-16)&mask;rr[1]=p;rr[7]=slot;rr[0]=get(p);rr[2]=get(rr[0]+100)
        last_a,last_b=rr[2],0x16b00 if rr[2]==0x16b00 else 0x16b1c
        n=10 if rr[2]==0x16b00 else 12
        if rr[2] in (0x16b00,0x16b1c):
            rr[2]=149;rr[0]=get(p);rr[4]=(rr[4]-4)&mask;store(rr[4],CODE+0x2d319);pc=0x30ea0;n+=3
        else:
            last_a,last_b=get(p+112),7;n+=2
            if last_a==7:
                last_a,last_b=get(slot),0x1617c;n+=2
                if last_a==last_b:
                    rr[2]=11;rr[0]=get(p);rr[4]=(rr[4]-4)&mask;store(rr[4],CODE+0x2d333);pc=0x3f370;n+=3
                else:pc=0x2d333
            else:pc=0x2d333
        if full:
            require(pc==0x2d333,'full idle must pass entry')
            bob=signed(amplitude);index=(time<<7)&8191;half=index&4095
            xx=((bob*trig[index+2048])>>16)+65536;yy=((bob*trig[half])>>16)+2097152
            store(p+188,0);store(slot+8,xx);store(slot+12,yy)
            rr=original.copy();rr[0]=yy&mask;rr[2]=((bob*trig[half])>>32)&mask;rr[4]=(sp+4)&mask
            pc=0x2d095;n+=29
        else:
            diff=(last_a-last_b)&mask
            expected_flags=(int(diff==0)<<6)|((diff>>31)<<7)|(int(((last_a^last_b)&(last_a^diff))>>31)<<11)|int(last_a<last_b)
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==expected_flags,f'flags/{i}')
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==data for a,data in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}')
        counts[pc]+=1
    return dict(entry_cases=entry_count,full_idle_cases=512,endpoints={hex(k):v for k,v in counts.items()},all_registers=True,entry_modeled_flags=True,ordered_writes=True,mutable_memory_frame=True,unaligned_wrapping_and_aliasing_stacks=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    def extract(name,key):return extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/name).read_text()))[key]
    raw=extract('original-weapon-ready-entry.json','entry')
    gate=extract('original-weapon-ready-gate.json','gate');idle=extract('original-weapon-ready.json','idle')
    _,table=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-weapon-ready-entry';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-ready-gate')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponReadyEntry'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,gate,idle,table) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope='Ready entry through pose/sound CALLs or decision boundary; uninterrupted no-reset idle and raising/nested returns under explicit post-prologue relations. Reset/sound callees and invariant transport remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: ready entry, pose/sound gates, and uninterrupted idle/raising joins.')
if __name__=='__main__':main()

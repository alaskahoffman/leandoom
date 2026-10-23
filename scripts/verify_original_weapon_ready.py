#!/usr/bin/env python3
"""Certify idle ready bobbing/return and the raising/nested-setter connections."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
import verify_original_thrust as thrust
ROOT,require=extraction.ROOT,extraction.require
NAMES=['idle_checked','raise_checked','setter_checked','machine_checked','live_checked','raising_checked','nested_checked','flash_checked']
NAMES+=['Doom.Proofs.WeaponReady.'+n for n in ['decoded','bob_execution','return_execution','execution','cleared_read','index_initial','cosine_value','horizontal_read','coordinates','frame','live_result']]
NAMES+=['Doom.Proofs.E1M1WeaponReady.'+n for n in ['contains_ready','contains_raise','contains_prior','contains_setter','raise_next_execution','finish_setter_execution','raised_idle_return_execution','raised_idle_flash']]

def certificate(raw,raise_code,setter):
    text='''import Doom.Proofs.E1M1WeaponReady
namespace Doom.Verification.ExtractedWeaponReady
open Doom Doom.Proofs X86 X86Memory X86Control
'''
    for label,bs,definition in [('idle',raw,'WeaponReady.code'),('raise',raise_code,'WeaponRaise.code'),('setter',setter,'PspriteSetter.code')]:
        text+=f'def {label}Bytes : List UInt8 := ['+','.join(hex(b) for b in bs)+f']\ntheorem {label}_checked : {label}Bytes={definition} := by decide\n'
    text+='''theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 23 ∧ X86Routine.Prefix (WeaponReady.bytesProgram idleBytes) [] n ⟨s,f,0x2d392⟩ (WeaponReady.result s) := by
  rw [idle_checked]; exact WeaponReady.execution s f
 theorem live_checked (s : X86Memory.State) (v : Weapon.State) (bob : Fixed) (time : Int32)
    (h : WeaponReady.Inputs s bob time) :
    load32 (WeaponReady.result s).core.memory (WeaponReady.location s 0)=0 ∧
    load32 (WeaponReady.result s).core.memory (WeaponReady.location s 1)=(Weapon.readyIdle v bob time).weapon.x.raw.toBitVec ∧
    load32 (WeaponReady.result s).core.memory (WeaponReady.location s 2)=(Weapon.readyIdle v bob time).weapon.y.raw.toBitVec ∧
    (WeaponReady.result s).pc=0x2d095 ∧ (WeaponReady.result s).core.regs 4=s.regs 4+20 :=
  WeaponReady.live_result s v bob time h
 theorem raising_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 46 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReady.program [] n ⟨s,f,0x2d4d0⟩ (E1M1WeaponReady.raiseNext s) :=
  E1M1WeaponReady.raise_next_execution s f
 theorem nested_checked (s : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (ok : E1M1WeaponReady.raisedIdleReturn s=some t) :
    ∃ n, n ≤ 52 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReady.program [] n ⟨s,f,0x2d392⟩ t :=
  E1M1WeaponReady.raised_idle_return_execution s f t ok
 theorem flash_checked (s : X86Memory.State) (f : Option Flags) (u : X86Control.State)
    (p : Word) (v : Weapon.State) (ok : E1M1WeaponReady.raisedIdleReturn s=some u)
    (pc : u.pc=0x2dc95) (boundary : E1M1WeaponFlash.Boundary u.core p v)
    (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → E1M1FlashExpiry.Tables u.core.memory ∧
      E1M1FlashExpiry.Separated p (u.core.regs 4)) :
    ∃ n t, n ≤ 162 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReady.program [] n ⟨s,f,0x2d392⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) :=
  E1M1WeaponReady.raised_idle_flash s f u p v ok pc boundary supported expiry
'''
    return text+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponReady\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponReady.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,table,out):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d392);signed=lambda v:v if v<2**31 else v-2**32
    edges=[0,1,65535,65536,0x7fffffff,0x80000000,0xfffffffe,0xffffffff]
    cases=[(rng.getrandbits(32),((i%64)|(rng.getrandbits(26)<<6))) for i in range(16384)]
    cases += [(a,t) for a in edges for t in edges]
    cases += [(rng.getrandbits(32),rng.getrandbits(32)) for _ in range(256)]
    inp,outp=out/'inputs.txt',out/'live.txt';inp.write_text(''.join(f'{signed(a)} {signed(t)}\n' for a,t in cases))
    subprocess.run([str(ROOT/'scripts/lake'),'env','lean','--run',str(ROOT/'tests/reference/weapon-ready-probe.lean'),str(inp),str(outp)],cwd=ROOT,check=True)
    live=[tuple(map(int,r.split())) for r in outp.read_text().splitlines()];require(len(live)==len(cases),'probe length')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,HEAP=0x100000,0x600000
    for base,size in [(CODE,0x30000),(0,0x30000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    em.mem_write(CODE+0x2d392,raw);em.mem_write(0x5a84,table);em.mem_write(0x13584,struct.pack('<I',0x7a84))
    trig=struct.unpack('<10240i',table)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&0xffffffff)))
    def visit(e,a,_n,_d):
        if a==CODE+0x2d095:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    for i,((amplitude,time),(wantx,wanty,latch)) in enumerate(zip(cases,live)):
        p=HEAP+64+i%4;psp=HEAP+512+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=0xfffffff5
        elif i%13==0:sp=5
        blocks={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&0xffffffff)):
                z=(a+k)&0xffffffff;blocks[z&~4095][z&4095]=b
        rr=[rng.getrandbits(32) for _ in regs];rr[1]=p;rr[7]=psp;rr[4]=sp
        saved=[rng.getrandbits(32) for _ in range(4)]
        for k,v in enumerate(saved+[CODE+0x2d095]):put(sp+4*k,v)
        put(p+28,amplitude)
        for a,data in blocks.items():em.mem_write(a,bytes(data))
        em.mem_write(0x2cf80,struct.pack('<I',time))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        em.emu_start(CODE+0x2d392,CODE+0x30000,count=24)
        expected=[(p+188,4,0),(psp+8,4,wantx),(psp+12,4,wanty)]
        require(latch==0 and writes==expected,f'live writes/{i}')
        for a,_,v in expected:put(a,v)
        require(all(bytes(em.mem_read(a,4096))==data for a,data in blocks.items()),f'memory frame/{i}')
        rr[0]=wanty;rr[2]=((signed(amplitude)*trig[(time<<7)&4095])>>32)&0xffffffff
        rr[7],rr[6],rr[1],rr[3]=saved;rr[4]=(sp+20)&0xffffffff
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2d095 and len(visits)==23,f'return/count/{i}')
    return dict(cases=len(cases),all_64_bob_phases=True,all_registers=True,ordered_writes=True,mutable_memory_frame=True,
        scope='Original idle ready suffix versus production readyIdle, including fractional/negative bob, signed times, unaligned fields and wrapping stacks.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    def extract(name):return extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/name).read_text()))
    raw=extract('original-weapon-ready.json')['idle'];raise_code=extract('original-weapon-raise.json')['raise'];setter=extract('original-weapon-drop.json')['setter']
    _,table=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-weapon-ready';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-e1m1-weapon-flash')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponReady'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,raise_code,setter));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    table_check=thrust.check_tables(table)
    native=cross_check(raw,table,out) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),tables=table_check,cross_check=native,
      scope='Idle ready suffix to actual RET; A_Raise through setter dispatch/resume; conditional nested setter/raise/outer-setter returns through flash observations under the post-weapon boundary. Earlier ready gates and full live weapon/flash correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: idle ready bobbing, actual return and nested setter connections.')
if __name__=='__main__':main()

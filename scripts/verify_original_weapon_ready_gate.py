#!/usr/bin/env python3
"""Certify ready decisions against DOS instructions and the production helper."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','machine_checked','live_checked','joined_checked']
NAMES+=['Doom.Proofs.WeaponReadyGate.'+n for n in ['decoded','choice_execution','trigger_execution','lower_execution','fire_execution','execution','live_lowering','supported_not_held','live_decision','idle_result','lower_live','fire_live']]
NAMES+=['Doom.Proofs.E1M1WeaponReadyGate.'+n for n in ['contains_gate','contains_prior','idle_gate','idle_execution','nested_execution','idle_live']]

def certificate(raw):
    return '''import Doom.Proofs.E1M1WeaponReadyGate
namespace Doom.Verification.ExtractedWeaponReadyGate
open Doom Doom.Proofs X86 X86Memory X86Control
 def extracted : List UInt8 := ['''+','.join(hex(b) for b in raw)+''']
 theorem bytes_checked : extracted=WeaponReadyGate.code := by decide
 theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤16 ∧ X86Routine.Prefix (WeaponReadyGate.bytesProgram extracted) [] n ⟨s,f,0x2d333⟩ (WeaponReadyGate.result s) := by
  rw [bytes_checked]; exact WeaponReadyGate.execution s f
 theorem live_checked (s : X86Memory.State) (w : Fin 3) (p : Nat) (hp : Int32) (a : Bool)
    (h : WeaponReadyGate.Inputs s w p hp a) :
    (WeaponReadyGate.result s).pc = match Weapon.readyDecision p hp a with
      | .lower => 0x2d040 | .fire => 0x2d410 | .idle => 0x2d392 :=
  WeaponReadyGate.live_decision s w p hp a h
 theorem joined_checked (s : X86Memory.State) (f : Option Flags)
    (low : ¬WeaponReadyGate.lowering s) (a : WeaponReadyGate.attack s=0) :
    ∃ n, n≤39 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyGate.program [] n ⟨s,f,0x2d333⟩ (WeaponReady.result s) :=
  E1M1WeaponReadyGate.idle_execution s f low a
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponReadyGate\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponReadyGate.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,out):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d333);mask=0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,HEAP=0x100000,0x600000
    for base,size in [(CODE,0x40000),(0,0x20000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    em.mem_write(CODE+0x2d333,raw)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    exits={0x2d040,0x2d410,0x2d392,0x2d39c};writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE in exits:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    cases=[(p,h,w,l,b) for p in [0,1,2,10,0xffffffff] for h in [0,1,100,0xffffffff] for w in range(9) for l in [0,1,0xffffffff] for b in [0,1,2,255]]
    cases += [(rng.choice([0,1,2,10]),rng.choice([0,100,rng.getrandbits(32)]),rng.randrange(9),rng.choice([0,1,rng.getrandbits(32)]),rng.randrange(256)) for _ in range(8192)]
    counts={k:0 for k in exits};probe=[];want=[]
    for i,(pending,hp,w,latch,buttons) in enumerate(cases):
        p=HEAP+64+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        elif i%17==0:sp=p+192 # return-address store aliases the attack latch
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&mask)):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        put(p+116,pending);put(p+32,hp);put(p+112,w);put(p+188,latch)
        pages[HEAP][p+15-HEAP]=buttons
        for a,data in pages.items():em.mem_write(a,bytes(data))
        down=rng.getrandbits(32);em.mem_write(0x12d98+24*w,struct.pack('<I',down))
        rr=[rng.getrandbits(32) for _ in regs];rr[1]=p;rr[4]=sp
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        em.emu_start(CODE+0x2d333,CODE+0x40000,count=17)
        expected=[]
        if pending!=10 or hp==0:
            pc=0x2d040;n=(2 if pending!=10 else 4)+7
            rr[0]=p;rr[2]=0;rr[3]=down;rr[4]=(sp-4)&mask;expected=[(rr[4],4,CODE+0x2d35b)]
        elif not buttons&1:pc=0x2d392;n=6
        else:
            n=8
            if latch:
                rr[6]=w;n+=3 if w==4 else 5
            if latch and w in (4,6):pc=0x2d39c
            else:
                pc=0x2d410;n+=3;rr[0]=p;rr[4]=(sp-4)&mask
                expected=[(p+188,4,1),(rr[4],4,CODE+0x2d38d)]
        require(writes==expected,f'ordered writes/{i}: {writes} != {expected}')
        for a,_,v in expected:put(a,v)
        require(all(bytes(em.mem_read(a,4096))==data for a,data in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,f'endpoint/count/{i}')
        counts[pc]+=1
        if w<3 and pending in [0,1,2,10]:
            signed=hp if hp<2**31 else hp-2**32
            probe.append(f'{9 if pending==10 else pending} {signed} {buttons&1}\n');want.append(pc)
    inp=out/'inputs.txt';dst=out/'live.txt';inp.write_text(''.join(probe))
    subprocess.run([str(ROOT/'scripts/lake'),'env','lean','--run',str(ROOT/'tests/reference/weapon-ready-gate-probe.lean'),str(inp),str(dst)],cwd=ROOT,check=True)
    require([int(s) for s in dst.read_text().splitlines()]==want,'production decision probe')
    return dict(cases=len(cases),live_cases=len(want),endpoints={hex(k):v for k,v in counts.items()},all_registers=True,ordered_writes=True,mutable_memory_frame=True,unaligned_and_wrapping_stacks=True,stack_latch_alias=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,json.loads((ROOT/'tests/reference/original-weapon-ready-gate.json').read_text()))['gate']
    out=ROOT/'artifacts/original-weapon-ready-gate';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-ready')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponReadyGate'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,out) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope='Ready decisions after pose/chainsaw gates, to actual lower/fire calls or bob entries. Supported live helper correspondence and idle return join. Earlier entry gates and callee behavior are separate obligations.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: ready decisions, production helper correspondence and idle return join.')
if __name__=='__main__':main()

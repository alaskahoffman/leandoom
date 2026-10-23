#!/usr/bin/env python3
"""Verify the real standing-pose setter, arbitrary returns, and ready continuation."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
import verify_original_thrust as thrust
ROOT,require=extraction.ROOT,extraction.require
NAMES=['setter_checked','state_checked','machine_checked','live_checked','joined_checked']
NAMES+=['Doom.Proofs.ActorSetterReturn.'+n for n in ['epilogue','execution','memory_frame','fields']]
NAMES+=['Doom.Proofs.E1M1WeaponReadyReset.'+n for n in ['table_decoded','live_pose','contains_setter','contains_prior','setter_execution','reset_execution','weapon_preserved','gate_execution','idle_execution','nested_execution','raise_reset_return']]

def table_data(binary,profile,spec):
    le=int(profile['le_offset'],16);u32=lambda p:struct.unpack_from('<I',binary,p)[0]
    data=struct.unpack_from('<6I',binary,le+u32(le+0x40)+48)
    require(data==(0x85e10,0x70000,0x2043,71,38,0),'unexpected data object')
    row=spec['state'];start=int(row['offset'],16)
    require(row['index']==149 and start==0x16a74,'wrong standing-state address')
    raw=bytearray()
    for p in range(start,start+28):
        at=le+u32(le+0x48)+4*(70+p//4096)
        require(binary[at+3]==0,'unsupported table page');physical=int.from_bytes(binary[at:at+3],'big')
        require(physical>0,'unmapped table page')
        offset=int(profile['data_pages_offset'],16)+(physical-1)*4096+p%4096
        require(offset<len(binary),'truncated table page');raw.append(binary[offset])
    require(raw.hex()==row['hex'],'standing-state bytes differ')
    require(struct.unpack('<7I',raw)==(28,0,0xffffffff,0,0,0,0),'wrong standing-state fields')
    relocs=extraction.fixups(binary,range(70+start//4096,70+(start+27)//4096+1))
    require(not any(max(70*4096+start,p)<min(70*4096+start+28,p+4) for p,_,_ in relocs),'unexpected standing-state relocation')
    return bytes(raw)

def certificate(raw,state):
    return '''import Doom.Proofs.E1M1WeaponReadyReset
namespace Doom.Verification.ExtractedWeaponReadyReset
open Doom Doom.Proofs X86 X86Memory X86Control
 def setter : List UInt8 := ['''+','.join(hex(b) for b in raw)+''']
 def stateBytes : List UInt8 := ['''+','.join(hex(b) for b in state)+''']
 theorem setter_checked : setter=Doom19.setMobjStateBytes := by decide
 theorem state_checked : stateBytes=E1M1WeaponReadyReset.stateBytes := by decide
 theorem machine_checked (p : DeathSetter.Entry) (s : X86Memory.State) (f : Option Flags) (ret : Word)
    (h : DeathSetter.SetterInputs p s ret) :
    ∃ n, n≤24 ∧ X86Routine.Prefix (PainSetter.bytesProgram setter) [] n ⟨s,f,0x30ea0⟩ (ActorSetterReturn.result p s ret) := by
  rw [setter_checked]; exact ActorSetterReturn.execution p s f ret h
 theorem live_checked (s : X86Memory.State) :
    DeathSetter.observeFields (E1M1WeaponReadyReset.returned s).core.memory (s.regs 0)=
      (BitVec.ofNat 32 (0x15a28+28*(PlayerAnim.enter 149).1.frame),(PlayerAnim.enter 149).1.tics.toBitVec,28,0) :=
  E1M1WeaponReadyReset.live_pose s
 theorem joined_checked (s : X86Memory.State) (f : Option Flags) (w : Fin 3)
    (reset : WeaponReadyEntry.needsReset (WeaponReadyEntry.prepared s))
    (h : DeathSetter.SetterInputs E1M1WeaponReadyReset.entry (E1M1WeaponReadyReset.call s).core 0x2d319)
    (weapon : WeaponReadyEntry.weapon (E1M1WeaponReadyReset.call s).core=BitVec.ofNat 32 w.val)
    (safe : ∀ b, b ∈ DeathSetter.writes (E1M1WeaponReadyReset.call s).core → BlockSummary.Apart ((E1M1WeaponReadyReset.call s).core.regs 1+112) b)
    (low : ¬WeaponReadyGate.lowering (E1M1WeaponReadyReset.afterReset s).core)
    (a : WeaponReadyGate.attack (E1M1WeaponReadyReset.afterReset s).core=0) :
    ∃ n, n≤89 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyReset.program [] n ⟨s,f,0x2d2f0⟩
      (WeaponReady.result (E1M1WeaponReadyReset.afterReset s).core) :=
  E1M1WeaponReadyReset.idle_execution s f w reset h weapon safe low a
'''+ '\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponReadyReset\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponReadyReset.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,state,entry,gate,idle,trigbytes):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x16a74);mask=0xffffffff;CODE,HEAP=0x100000,0x600000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(CODE,0x40000),(0,0x30000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    em.mem_write(CODE+0x30ea0,raw);em.mem_write(CODE+0x2d2f0,entry+gate+idle)
    em.mem_write(0x16a74,state);em.mem_write(0x5a84,trigbytes);em.mem_write(0x13584,struct.pack('<I',0x7a84))
    trig=struct.unpack('<10240i',trigbytes);signed=lambda v:v if v<2**31 else v-2**32
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[];ret=0
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if visits and a==ret:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    standalone,full_count=1024,1024
    for i in range(standalone+full_count):
        full=i>=standalone;frame=154+i%2
        p=HEAP+64+i%4;obj=HEAP+1024+i%4;slot=HEAP+512+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=1
        elif i%13==0:sp=0xfffffff5
        ret=CODE+0x2d095 if full else [0,1,0xffffffff,CODE+0x2d319,CODE+0x2a3f1,CODE+0x30ea0][i%6]
        pages={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&mask)):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        put(p,obj);put(obj+100,0x15a28+frame*28);put(p+112,i%3);put(slot,0x15b40);put(sp,ret)
        amplitude,time=rng.getrandbits(32),rng.getrandbits(32)
        if full:
            put(p+116,10);put(p+32,100);put(p+28,amplitude);pages[HEAP][p+15-HEAP]=0
        for a,data in pages.items():em.mem_write(a,bytes(data))
        em.mem_write(0x2cf80,struct.pack('<I',time))
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=p if full else obj;rr[2]=slot if full else 149;rr[4]=sp;original=rr.copy()
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        # Code hook stops before executing even a same-entry return target.
        em.emu_start(CODE+(0x2d2f0 if full else 0x30ea0),CODE+0x40000,count=90)
        expected=[]
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        if full:
            for k,r in enumerate([3,1,6,7],1):store(sp-4*k,rr[r])
            store(sp-20,CODE+0x2d319);callee_sp=(sp-20)&mask
        else:callee_sp=sp
        store(callee_sp-4,rr[3]);store(callee_sp-8,rr[6])
        for off,v in [(100,0x16a74),(96,0xffffffff),(36,28),(40,0)]:store(obj+off,v)
        rr[0]=1;rr[2]=0;rr[4]=(sp+4)&mask;n=24
        if full:
            bob=signed(amplitude);index=(time<<7)&8191;half=index&4095
            xx=((bob*trig[index+2048])>>16)+65536;yy=((bob*trig[half])>>16)+2097152
            store(p+188,0);store(slot+8,xx);store(slot+12,yy)
            rr=original.copy();rr[0]=yy&mask;rr[2]=((bob*trig[half])>>32)&mask;rr[4]=(sp+4)&mask
            n=68 if frame==154 else 70
        else:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x80,f'flags/{i}')
        require(writes==expected,f'ordered writes/{i}')
        require(all(bytes(em.mem_read(a,4096))==data for a,data in pages.items()),f'memory frame/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==ret and len(visits)==n,f'endpoint/count/{i}')
    return dict(setter_cases=standalone,full_reset_idle_cases=full_count,arbitrary_return_targets=[hex(v) for v in [0,1,0xffffffff,0x2d319,0x2a3f1,0x30ea0]],both_firing_poses=True,all_registers=True,ordered_writes=True,mutable_memory_frame=True,unaligned_and_wrapping_stacks=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    def extract(name,key):return extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/name).read_text()))[key]
    raw=extract('original-player-animation.json','setMobjStateBytes')
    state=table_data(binary,profile,json.loads((ROOT/'tests/reference/original-weapon-ready-reset.json').read_text()))
    entry=extract('original-weapon-ready-entry.json','entry');gate=extract('original-weapon-ready-gate.json','gate');idle=extract('original-weapon-ready.json','idle')
    _,trig=thrust.extract(binary,profile,json.loads((ROOT/'tests/reference/original-thrust.json').read_text()))
    out=ROOT/'artifacts/original-weapon-ready-reset';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:subprocess.run([str(ROOT/'scripts/verify-original-weapon-ready-entry')],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1WeaponReadyReset'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,state));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,state,entry,gate,idle,trig) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope='General no-action nonzero-tic actor setter with arbitrary actual return; production standing pose; ready entry through reset, sound rejection, idle and conditional nested returns. Explicit table, separation and post-reset idle boundaries remain.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: actual pose reset, reusable actor returns and ready continuation.')
if __name__=='__main__':main()

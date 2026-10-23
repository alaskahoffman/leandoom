#!/usr/bin/env python3
"""Certify original A_Raise arithmetic, return, and ready-state setter dispatch."""
import argparse,json,random,re,struct,subprocess
import verify_original_inline_thrust as extraction
from verify_original_weapon_drop import table_data
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','tables_checked','machine_checked','live_checked','dispatch_checked']
NAMES+=['Doom.Proofs.WeaponRaise.'+n for n in ['decoded','branch_execution','return_execution','dispatch_execution','execution','read_store','read_return','live_step','live_result','frame']]

def certificate(raw,tables,spec):
    s='''import Doom.Proofs.OriginalWeaponRaise
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedWeaponRaise
open Doom Doom.Proofs WeaponRaise X86 X86Memory X86Control
'''
    s+='def original : List UInt8 := ['+','.join(hex(b) for b in raw['raise'])+']\n'
    for name,bs in tables.items():s+='def '+name+' : Array UInt8 := #['+','.join(hex(b) for b in bs)+']\n'
    s+='def tableMemory : Memory := fun a =>\n'
    for name,u in spec['tables'].items():
        lo=int(u['offset'],16);s+=f'  if {lo} ≤ a.toNat ∧ a.toNat < {lo+4} then {name}[a.toNat-{lo}]!.toBitVec else\n'
    s+='  0\n'
    s+='''theorem bytes_checked : original=code := by decide
 theorem tables_checked (w : Fin 3) :
    load32 tableMemory (BitVec.ofNat 32 (0x12d9c+24*w.val))=BitVec.ofNat 32 (Weapon.ready w.val) := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide
 theorem machine_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n ≤ 17 ∧ X86Routine.Prefix (bytesProgram original) [] n ⟨s,f,0x2d4d0⟩ (result s) := by
  rw [bytes_checked]; exact execution s f
 theorem live_checked (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y) :
    load32 (result s).core.memory (yAddress s)=(Weapon.raiseStep y).1.raw.toBitVec ∧
    (result s).pc=(if (Weapon.raiseStep y).2 then 0x2d040 else 0x2d095) ∧
    PlayerHeight.Frame s.memory (result s).core.memory (writes s) := by
  have post := live_result s w y h
  refine ⟨post.1,?_,frame s⟩
  cases ready : (Weapon.raiseStep y).2 <;> simp [ready] at post ⊢ <;> exact post.2.1
 theorem dispatch_checked (s : X86Memory.State) (w : Fin 3) (y : Fixed) (h : Inputs s w y)
    (ready : (Weapon.raiseStep y).2=true) :
    (result s).pc=0x2d040 ∧ (result s).core.regs 0=s.regs 0 ∧ (result s).core.regs 2=(0#32) ∧
      (result s).core.regs 3=BitVec.ofNat 32 (Weapon.ready w.val) ∧
      (result s).core.regs 4=s.regs 4-(12#32) ∧
      load32 (result s).core.memory ((result s).core.regs 4)=(0x2d50d#32) := by
  have post := (live_result s w y h).2
  simpa only [ready,Bool.true_eq,if_true] using post
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedWeaponRaise\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedWeaponRaise.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,tables,spec,out):
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2d4d0)
    cases=[((hi<<16)|rng.randrange(65536),hi%3) for hi in range(65536)]
    cases += [((n+d)&0xffffffff,w) for n in [0,0x200000,0x260000,0x80000000,0x80060000,0xffffffff] for d in [-65536,-1,0,1,65535] for w in range(3)]
    cases += [(rng.getrandbits(32),rng.randrange(3)) for _ in range(256)]
    inp,outp=out/'inputs.txt',out/'live.txt'
    inp.write_text(''.join(str(v if v<2**31 else v-2**32)+'\n' for v,_ in cases))
    subprocess.run([str(ROOT/'scripts/lake'),'env','lean','--run',str(ROOT/'tests/reference/weapon-raise-probe.lean'),str(inp),str(outp)],cwd=ROOT,check=True)
    live=[tuple(map(int,r.split())) for r in outp.read_text().splitlines()];require(len(live)==len(cases),'probe length')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);CODE,DATA,HEAP=0x100000,0x10000,0x600000
    for base,size in [(CODE,0x30000),(DATA,0x10000),(HEAP,4096),(0,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    em.mem_write(CODE+0x2d4d0,raw['raise'])
    for name,bs in tables.items():em.mem_write(int(spec['tables'][name]['offset'],16),bs)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&0xffffffff)))
    def visit(e,a,_n,_d):
        if a in [CODE+0x2d040,CODE+0x2d095]:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    counts={'raising':0,'ready':0}
    for i,((height,w),(want,ready)) in enumerate(zip(cases,live)):
        player=HEAP+64+i%4;psp=HEAP+512+i%4;sp=HEAP+3072+i%4
        if i%11==0:sp=5
        elif i%13==0:psp=0xfffffff0
        ya=(psp+12)&0xffffffff
        blocks={a:bytearray(rng.randbytes(4096)) for a in [0,HEAP,0xfffff000]}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&0xffffffff)):
                z=(a+k)&0xffffffff;blocks[z&~4095][z&4095]=b
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=player;rr[2]=psp;rr[4]=sp
        put(player+112,w);put(ya,height);put(sp,CODE+0x2d095)
        for a,data in blocks.items():em.mem_write(a,bytes(data))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        em.emu_start(CODE+0x2d4d0,CODE+0x30000,count=18)
        advanced=(height-0x60000)&0xffffffff
        expected=[((sp-4)&0xffffffff,4,rr[3]),((sp-8)&0xffffffff,4,rr[1]),(ya,4,advanced)]
        if ready:
            expected += [(ya,4,0x200000),((sp-12)&0xffffffff,4,CODE+0x2d50d)]
            rr[1]=rr[3]=[2,10,18][w];rr[2]=0;rr[4]=(sp-12)&0xffffffff;target=CODE+0x2d040;counts['ready']+=1
        else:rr[4]=(sp+4)&0xffffffff;target=CODE+0x2d095;counts['raising']+=1
        require(writes==expected,f'ordered writes/{i}')
        for a,_,v in expected:put(a,v)
        require(all(bytes(em.mem_read(a,4096))==data for a,data in blocks.items()),f'memory frame/{i}')
        require(struct.unpack('<I',em.mem_read(ya,4))[0]==want,f'live height/{i}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{i}')
        require(em.reg_read(x.UC_X86_REG_EIP)==target,f'branch/{i}')
        require(len(visits)==(17 if ready else 11),f'instruction count/{i}')
    return dict(cases=len(cases),groups=counts,all_high_halves=True,all_registers=True,ordered_writes=True,full_mapped_mutable_memory=True,
                scope='Original A_Raise versus production raiseStep, including wrapping stacks and unaligned/fractional heights; ready paths stop at the real setter CALL.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-weapon-raise.json').read_text());exe=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,exe);raw=extraction.extract(binary,exe,spec);tables=table_data(binary,exe,spec)
    out=ROOT/'artifacts/original-weapon-raise';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalWeaponRaise'],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,check=True)
    p=out/'Checked.lean';p.write_text(certificate(raw,tables,spec));r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(p)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,tables,spec,out) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
      scope='Original A_Raise to in-progress RET or ready setter CALL, with live height/decision/arguments and memory frame. Ready action and full weapon/flash composition remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original weapon raising, live height/decision and ready-state dispatch.')
if __name__=='__main__':main()

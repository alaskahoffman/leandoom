#!/usr/bin/env python3
"""Pin and certify P_PathTraverse X-axis direction, portion and slope."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','abs_checked','div_checked','execution_checked']
PROOFS=['OriginalAbs.'+n for n in ['execution','registers','memory','wrapped','checked']]
PROOFS+=['OriginalPathXStep.'+n for n in ['decoded','selection_execution','moving_execution','execution','input_observe','moving_observe','division_success','live']]
PROOFS+=['E1M1PathXStep.'+n for n in ['first_xstep_execution','inputs_from_init','first_xstep_correspondence']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1PathXStep
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPathXStep
open Doom Doom.Proofs X86 X86Memory X86Control OriginalPathXStep
'''
    for name in ['xstep','abs','division']:
        s+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
    s+='''theorem bytes_checked : xstepBytes=code := by decide
theorem abs_checked : absBytes=OriginalAbs.code := by decide
theorem div_checked : divisionBytes=Doom19.fixedDivBytes := by decide
def extractedProgram (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if 0x2c96c≤pc ∧ pc<0x2c9d3 then bytesProgram xstepBytes pc
  else if 0x418d8≤pc ∧ pc<0x418df then OriginalAbs.bytesProgram absBytes pc
  else OriginalDivMemory.bytesProgram divisionBytes pc
theorem execution_checked (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n, n≤45 ∧ X86Routine.Prefix extractedProgram [] n ⟨s,f,0x2c96c⟩ (result s) := by
  have same : extractedProgram=program := by
    funext pc
    simp only [extractedProgram,program,localProgram,OriginalAbs.program,OriginalDivMemory.program,
      bytes_checked,abs_checked,div_checked]
  rw [same]; exact execution s f safe
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathXStep\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedPathXStep.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected output')

def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x50000)
    for name,start in [('xstep',0x2c96c),('abs',0x418d8),('division',0x1d180)]:
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],start))
        require(b''.join(bytes(i.bytes) for i in listing)==raw[name],'decoder mismatch')
        em.mem_write(CODE+start,raw[name])
    bases=[0,HEAP,0xfffff000]
    for a in bases:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c96c);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    signed=lambda v:v if v<0x80000000 else v-(1<<32)
    absword=lambda v:(-v)&MASK if signed(v)<0 else v
    groups=dict(same=0,right=0,left=0,saturated=0,divided=0,negative_abs=0,int_min_abs=0)
    edges=[0,1,0xffff,0x10000,0x7fffffff,0x80000000,0x80000001,0xffffffff]
    for i in range(1024):
        pages={a:bytearray(rng.randbytes(4096)) for a in bases}
        def put(a,v):
            for j,b in enumerate(struct.pack('<I',v&MASK)):
                q=(a+j)&MASK;pages[q&~4095][q&4095]=b
        def read(a):
            return int.from_bytes(bytes(pages[((a+j)&MASK)&~4095][((a+j)&MASK)&4095] for j in range(4)),'little')
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[HEAP+1024,HEAP+1025,1,0xfffffffd][i%4];rr[4]=sp
        dx=edges[(i//3)%len(edges)] if i<512 else rng.getrandbits(32)
        rr[5]=(rr[6]+dx)&MASK
        # This harness covers successful arithmetic; #DE has its own FixedDiv suite.
        if dx==0 and rr[2]==0x80000000:rr[2]=0x80000001
        start=[0,0xffffffff,0x80000000,0x7fffffff][(i//3)%4]
        end=start if i%3==0 else (0x7fffffff if i%3==1 else 0x80000000)
        put(sp+12,start);put(sp+20,end);put(sp+8,rng.getrandbits(32))
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        expected=[]
        def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
        forward=signed(end)>signed(start);back=signed(end)<signed(start)
        wanted=rr.copy();wanted[0]=dx;wanted[3]=end
        if not forward and not back:
            groups['same']+=1;wanted[0]=0x1000000;wanted[2]=0;wanted[3]=0x10000
            store(sp+32,0);count=10
        else:
            groups['right' if forward else 'left']+=1
            negative=signed(dx)<0;groups['negative_abs']+=negative;groups['int_min_abs']+=dx==0x80000000
            store(sp-4,CODE+(0x2c97f if forward else 0x2c9a7))
            denominator=absword(dx);numerator=rr[2]
            store(sp,denominator);store(sp+32,1 if forward else MASK)
            portion=0x10000 if forward else read(sp+8)
            store(sp-4,CODE+(0x2c99a if forward else 0x2c9c1))
            store(sp-8,portion);store(sp-12,rr[1]);store(sp-16,rr[6])
            aa=signed(absword(numerator));bb=signed(absword(denominator))
            if aa>>14>=bb:
                groups['saturated']+=1;answer=0x80000000 if signed(numerator^denominator)<0 else 0x7fffffff
                remainder=MASK if signed(denominator)<0 else 0
            else:
                groups['divided']+=1;dividend=signed(numerator)*65536;divisor=signed(denominator)
                require(divisor!=0,'unexpected fault in success suite')
                q=abs(dividend)//abs(divisor)*(-1 if (dividend<0)!=(divisor<0) else 1)
                require(-2147483648<=q<=2147483647,'unexpected overflow in success suite')
                answer=q&MASK;remainder=(dividend-q*divisor)&MASK
            wanted[0]=answer;wanted[2]=remainder
            wanted[3]=(portion-read(sp+8))&MASK if forward else portion
            count=43+negative
        writes.clear();visits.clear()
        em.emu_start(CODE+0x2c96c,CODE+0x2c9d3,count=45)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2c9d3,'wrong stop')
        require(len(visits)==count,'wrong instruction count')
        require([em.reg_read(r) for r in regs]==wanted,'wrong registers')
        require(writes==expected,'wrong write order')
        for a,b in pages.items():require(em.mem_read(a,4096)==b,'wrong mapped data memory')
    require(all(groups.values()),'missing branch coverage')
    return {'total_cases':1024,'groups':groups,
      'checks':'all registers, all mapped data memory, ordered stack writes, both real calls/returns, three directions, saturation/division, INT_MIN helper, unaligned/wrapping stacks',
      'scope':'successful machine arithmetic; engine rejects abs(INT_MIN); stops before first Y-intercept multiplication; flags not compared'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-path-xstep.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(3,))
    out=ROOT/'artifacts/original-path-xstep';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PathXStep'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);(out/'axioms.log').write_text(result.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
      'scope':'X-axis setup <=45 instructions including abs and FixedDiv; joined firing prefix <=268. Production xStep success supplies division safety; coordinate/stack encoding and the earlier prefix assumptions remain explicit. Y intercept/setup, cell visitation, callbacks and whole-game equivalence remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original X-axis setup, real helper/division calls and firing join, kernel certificates and axiom audit.')
    if args.cross_check:print('Native X-axis cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:print(e.stdout or '');print(e.stderr or '');raise

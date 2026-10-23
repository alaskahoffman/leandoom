#!/usr/bin/env python3
"""Certify the original line-fraction setup and complete intersection helper."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['helper_checked','setup_checked','division_checked','execution_checked']
PROOFS=['OriginalInterceptVector.'+n for n in ['decoded','contains_div','prepare_execution','den_execution','num_execution','div_return','divided_execution','zero_execution','body_execution','execution','prepare_frame','operands','safe_of_success','live','inner_frame','body_regs','returned','frame']]
PROOFS+=['OriginalLineFraction.'+n for n in ['decoded','contains_helper','setup_execution','execution','returned','live','setup_memory','local_frame','encoded']]

PROOFS+=['E1M1LineFraction.'+n for n in ['contains_prior','contains_fraction','continue_execution','line_fraction_execution','ready','crossed_live']]

def certificate(raw):
    source="""import Doom.Proofs.E1M1LineFraction
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedInterceptVector
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for name,target in [('helper','OriginalInterceptVector.code'),('setup','OriginalLineFraction.code'),('division','Doom19.fixedDivBytes')]:
        source+='def '+name+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Code='+target+' := by decide\n'
    source+="""theorem execution_checked (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalInterceptVector.Safe (OriginalLineFraction.setup s)) :
    ∃ n≤80, X86Routine.Prefix (OriginalLineFraction.bytesProgram setupCode) [] n
      ⟨s,f,0x2c691⟩ (OriginalLineFraction.result s) := by
  rw [setup_checked]; exact OriginalLineFraction.execution s f safe
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedInterceptVector\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedInterceptVector.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected output')


def extracted():
    spec=json.loads((ROOT/'tests/reference/original-intercept-vector.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    div=json.loads((ROOT/'tests/reference/original-div-memory.json').read_text())
    raw['division']=extraction.extract(binary,profile,div)['division']
    return spec,profile,raw

def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x50000)
    for name,start in [('setup',0x2c691),('helper',0x2c2d0),('division',0x1d180)]:
        code=raw[name];listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
        require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
        em.mem_write(CODE+start,code)
    addresses=[0,0x2b000,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c2d0);writes=[];visits=[];sub_flags=[];interrupts=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&((1<<(8*size))-1))))
    def visit(_,a,size,data):
        visits.append(a-CODE)
        if a-CODE==0x2c2fb:sub_flags.append(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1)
    em.hook_add(u.UC_HOOK_CODE,visit)
    def interrupt(machine,number,data):
        interrupts.append(number);machine.emu_stop()
    em.hook_add(u.UC_HOOK_INTR,interrupt)
    groups=dict(setup=0,direct=0,zero=0,divide=0,saturate=0,fault=0,stack_alias=0,wrapped_stack=0,negative=0)
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    mul=lambda a,b:((signed(a)*signed(b))>>16)&MASK
    high=lambda a,b:((signed(a)*signed(b))>>32)&MASK
    shift=lambda a:(signed(a)>>8)&MASK
    # Restore internal exception state too: a previous #DE must not turn the
    # next independent fault case into a spurious double fault.
    baseline=em.context_save()
    for i in range(2048):
        em.context_restore(baseline)
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v):
            for k,b in enumerate((v&MASK).to_bytes(4,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(4))
        setup=bool(i%2);mode=(i//2)%8
        p,q,line,v=HEAP+512,HEAP+768,HEAP+1024,HEAP+1088
        sp=[HEAP+256,HEAP+259,0,1,0xfffffff1,HEAP+528][(i//16)%6]
        a,b=[[rng.getrandbits(32) for _ in range(4)] for _ in range(2)]
        if mode==0:a[2:]=[0,0] # parallel/zero denominator
        if mode==1:
            a=[0,0,65536,0];b=[32768,0,0,65536] # exact 1/2
        if mode==2:
            a=[0,0,1,0];b=[0x02000000,0,0,0x40000000] # INT_MIN numerator -> IDIV fault
        if mode==3:
            a=[0,0,256,0];b=[0x7fffffff,0,0,65536] # guard saturation
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=sp
        if setup:
            p=0x2ba10;q=sp;rr[1]=line
            put(line,v);put(line+8,b[2]);put(line+12,b[3]);put(v,b[0]);put(v+4,b[1])
        for j,val in enumerate(a):put(p+4*j,val)
        if not setup:
            for j,val in enumerate(b):put(q+4*j,val)
            rr[0]=p;rr[2]=q;put(sp,CODE+0x4f000)
        for address,page in pages.items():em.mem_write(address,bytes(page))
        for reg,val in zip(regs,rr):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8c3 if i%3==0 else 2)
        wanted=rr.copy();expected=[];count=0
        def store(a,val):expected.append((a&MASK,4,val&MASK));put(a,val)
        def push(val):wanted[4]=(wanted[4]-4)&MASK;store(wanted[4],val)
        if setup:
            groups['setup']+=1
            wanted[0]=get(get(wanted[1]));store(sp,wanted[0])
            wanted[0]=get(get(wanted[1])+4);store(sp+4,wanted[0])
            wanted[0]=get(wanted[1]+8);store(sp+8,wanted[0])
            wanted[0]=get(wanted[1]+12);wanted[2]=sp;store(sp+12,wanted[0])
            wanted[0]=0x2ba10;push(CODE+0x2c6bb);count=13
        else:groups['direct']+=1
        hsp=wanted[4];entry=wanted.copy()
        for r in [3,1,6,7,5]:push(wanted[r])
        wanted[6]=wanted[0];wanted[1]=wanted[2];p=wanted[6];q=wanted[1]
        aa=shift(get(q+12));bb=get(p+8);left=mul(aa,bb)
        aa=shift(get(q+8));bb=get(p+12);right=mul(aa,bb)
        den=(left-right)&MASK;wanted[0]=right;wanted[2]=high(aa,bb);wanted[3]=bb;wanted[7]=den
        flags=(int(den==0)<<6)|(int(bool(den&0x80000000))<<7)|(int(bool((left^right)&(left^den)&0x80000000))<<11)|int(left<right)
        count+=20 # seven preparation, twelve denominator, one JNE
        fault=False
        if den==0:
            wanted[0]=0;count+=2;groups['zero']+=1
        else:
            aa=shift((get(q)-get(p))&MASK);bb=get(q+12);wanted[5]=mul(aa,bb)
            aa=shift((get(p+4)-get(q+4))&MASK);bb=get(q+8);wanted[0]=(mul(aa,bb)+wanted[5])&MASK
            wanted[3]=bb;wanted[2]=den;push(CODE+0x2c32e);count+=16
            ds=wanted[4];num=wanted[0]
            for r in [3,1,6]:push(wanted[r])
            wanted[1]=num;wanted[3]=den
            absnum=(-num if signed(num)<0 else num)&MASK;absden=(-den if signed(den)<0 else den)&MASK
            wanted[6]=(signed(absnum)>>14)&MASK;wanted[0]=absden;wanted[2]=MASK if signed(den)<0 else 0
            if signed(wanted[6])<signed(absden):
                numerator=signed(num)*65536;divisor=signed(den)
                quot=(abs(numerator)//abs(divisor))*(-1 if (numerator<0)!=(divisor<0) else 1) if divisor else 0
                fault=not divisor or not(-2147483648<=quot<=2147483647)
                if fault:
                    groups['fault']+=1
                    # IDIV leaves these inputs visible when it faults.
                    wanted[0]=(num<<16)&MASK;wanted[2]=((signed(num)*65536)>>32)&MASK
                    count+=21
                else:
                    wanted[0]=quot&MASK;wanted[2]=(numerator-quot*divisor)&MASK
                    groups['divide']+=1;count+=25
            else:
                wanted[0]=0x80000000 if signed(den^num)<0 else 0x7fffffff
                groups['saturate']+=1;count+=25
            if not fault:
                for j,r in enumerate([6,1,3]):wanted[r]=get(ds-12+4*j)
                wanted[4]=(ds+4)&MASK
        if not fault:
            for j,r in enumerate([5,7,6,1,3]):wanted[r]=get(hsp-20+4*j)
            wanted[4]=(hsp+4)&MASK;stop=get(hsp);count+=6
            groups['negative']+=signed(wanted[0])<0
        else:stop=CODE+0x1d1bb
        groups['wrapped_stack']+=sp in [0,1,0xfffffff1]
        groups['stack_alias']+=sp==HEAP+528 and not setup
        writes.clear();visits.clear();sub_flags.clear();interrupts.clear()
        em.emu_start(CODE+(0x2c691 if setup else 0x2c2d0),0,count=count)
        require(interrupts==([0] if fault else []),f'case {i}: wrong hardware exception {interrupts}')
        require(em.reg_read(x.UC_X86_REG_EIP)==stop,f'case {i}: wrong stop {em.reg_read(x.UC_X86_REG_EIP):x} != {stop:x}')
        require(len(visits)==count,f'case {i}: wrong count {len(visits)} != {count}')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: wrong registers')
        require(writes==expected,f'case {i}: wrong ordered writes')
        require(sub_flags==[flags],f'case {i}: wrong SUB flags')
        for address,page in pages.items():require(em.mem_read(address,4096)==page,f'case {i}: wrong data memory')
    require(all(groups.values()),'missing branch coverage')
    return {'total_cases':2048,'groups':groups,'checks':'All eight registers, mapped byte memory, ordered writes, exact instruction count and PC. ZF/SF/OF/CF after denominator subtraction. Complete original FixedDiv, no stubs.','scope':'Helper and callback setup only. Native IDIV faults checked; the universal execution/live theorem is explicitly restricted to successful production arithmetic. Final flags outside the SUB check are not compared. Return words use explicit code-base normalization.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec,profile,raw=extracted();out=ROOT/'artifacts/original-intercept-vector';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineFraction'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Complete original intersection fraction and callback setup. Live result equality under encoded geometry, stack separation and successful arithmetic. Callback rejection, insertion, full game equivalence remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original intersection fraction; extracted bytes and strict axiom audit.')
    if args.cross_check:print('Native intersection cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise

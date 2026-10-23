#!/usr/bin/env python3
"""Certify both original second-point calls and same-side callback return."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['wide_checked','short_checked','return_checked','line_checked','divline_checked','execution_checked']
PROOFS=['OriginalLineSecondPoint.'+n for n in ['decoded','contains_divline','contains_line','wide_call_execution','short_call_execution','helper_return','second_execution','unwind_execution','gate_execution','execution','call_regs','call_memory','second_saved','second_frame','wide_inputs','short_inputs','second_values','same_side_none','live','frame','rejected_pc','rejection']]
PROOFS+=['E1M1LineSecondPoint.'+n for n in ['contains_prior','contains_second','continue_execution','line_test_execution','at_return','rejected_live','first_return_form','first_return_regs','first_return_frame','entry_inputs','callback_rejection']]

def certificate(raw):
    source='''import Doom.Proofs.E1M1LineSecondPoint
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineSecondPoint
open Doom Doom.Proofs X86 X86Memory X86Control OriginalLineSecondPoint
'''
    for name in ['wide','short','return','line','divline']:
        source+='def '+name+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        target=name+'Bytes' if name in ['wide','short','return'] else 'Original'+('Line' if name=='line' else 'Divline')+'Side.code'
        source+='theorem '+name+'_checked : '+name+'Code='+target+' := by decide\n'
    source+='''theorem execution_checked (wide : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤62 ∧ X86Routine.Prefix (bytesProgram wideCode shortCode returnCode) [] n
      ⟨s,f,startPc wide⟩ (result wide s) := by
  rw [wide_checked,short_checked,return_checked]; exact execution wide s f
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineSecondPoint\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedLineSecondPoint.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected output')

def extracted():
    spec=json.loads((ROOT/'tests/reference/original-line-second-point.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    for name in ['line','divline']:
        helper=json.loads((ROOT/f'tests/reference/original-{name}-side.json').read_text())
        raw[name]=extraction.extract(binary,profile,helper)['side']
    return spec,profile,raw

def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x50000)
    for name,start in [('wide',0x2c637),('short',0x2c65f),('return',0x2c711),('line',0x2c010),('divline',0x2c1e0)]:
        code=raw[name];listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
        require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
        em.mem_write(CODE+start,code)
    addresses=[0,0x2b000,0x2c000,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c637);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&((1<<(8*size))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _,a,size,data:visits.append(a-CODE))
    groups=dict(wide_reject=0,wide_continue=0,short_reject=0,short_continue=0,
                helper_axis=0,helper_shortcut=0,helper_product=0,stack_alias=0,wrapped_stack=0,endpoint_wrap=0)
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    edges=[0,1,255,256,65536,0xffffffff,0x80000000,0x7fffffff]
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v):
            for k,b in enumerate((v&MASK).to_bytes(4,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(4))
        wide=bool(i%2);rr=[rng.getrandbits(32) for _ in regs]
        line,v1,v2=HEAP+512,HEAP+1024,HEAP+1040
        sp=[HEAP+128,HEAP+131,0,1,0xfffffff1,0x2ba24 if wide else line+24][(i//2)%6]
        rr[4]=sp;rr[1]=line;rr[0]=(i//2)%2
        lx,ly=rng.getrandbits(32),rng.getrandbits(32)
        dx,dy=edges[(i//4)%8],edges[(i//32)%8]
        if i%7==0:dx=0
        if i%7==1:dy=0
        tx,ty,tdx,tdy=[rng.getrandbits(32) for _ in range(4)]
        if i%7==2:tdx=0
        if i%7==3:tdy=0
        if not wide:tdx=(signed(tdx)%2097153-1048576)&MASK;tdy=(signed(tdy)%2097153-1048576)&MASK
        put(line,v1);put(line+4,v2);put(line+8,dx);put(line+12,dy)
        put(v1,lx);put(v1+4,ly);put(v2,lx+dx);put(v2+4,ly+dy)
        for a,val in [(0x2ba10,tx),(0x2ba14,ty),(0x2ba18,tdx),(0x2ba1c,tdy)]:put(a,val)
        for off in [16,20,24,28,32]:put(sp+off,rng.getrandbits(32))
        put(sp+36,CODE+0x4f000)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for reg,val in zip(regs,rr):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|((i&1)<<6)|((i&2)<<10))
        wanted=rr.copy();expected=[]
        def store(a,val):expected.append((a&MASK,4,val&MASK));put(a,val)
        # Actual second-call argument preparation, retaining the first result in ESI.
        wanted[6]=wanted[0]
        if wide:
            vp=get(line+4);wanted[3]=0x2ba10;wanted[2]=get(vp+4);wanted[0]=get(vp);count=6
        else:
            wanted[2]=get(0x2ba14);wanted[5]=get(0x2ba1c);wanted[3]=get(0x2ba18)
            wanted[0]=get(0x2ba10);wanted[2]=(wanted[2]+wanted[5])&MASK
            wanted[0]=(wanted[0]+wanted[3])&MASK;wanted[3]=wanted[1];count=9
        ret=0x2c64b if wide else 0x2c683;store(sp-4,CODE+ret);wanted[4]=(sp-4)&MASK
        # Execute the complete previously proved helper, with its real save slots.
        entry=wanted.copy();hsp=wanted[4];ptr=wanted[3]
        for k,r in enumerate([1,6,7,5],1):store(hsp-4*k,wanted[r])
        origin=ptr if wide else get(ptr)
        ox,oy=signed(get(origin)),signed(get(origin+4));dx0,dy0=signed(get(ptr+8)),signed(get(ptr+12))
        px,py=signed(entry[0]),signed(entry[2])
        if dx0==0:
            value=int(dy0>0 if px<=ox else dy0<0);count+=19 if wide else 18
            if not wide:wanted[2]=origin
            groups['helper_axis']+=1
        elif dy0==0:
            value=int(dx0<0 if py<=oy else dx0>0);count+=21 if wide else 20
            groups['helper_axis']+=1
        else:
            ax,ay=(px-ox)&MASK,(py-oy)&MASK
            if wide and ((dy0&MASK)^(dx0&MASK)^ax^ay)&0x80000000:
                wanted[3]=ax^(dy0&MASK);wanted[2]=dx0&MASK
                value=int(bool(wanted[3]&0x80000000));count+=34 if value else 33
                groups['helper_shortcut']+=1
            else:
                shift=8 if wide else 16
                left=((dy0>>shift)*((signed(ax)>>8) if wide else signed(ax)))>>16
                product=((signed(ay)>>8) if wide else signed(ay))*(dx0>>shift)
                value=int(signed((product>>16)&MASK)>=signed(left&MASK))
                wanted[3]=(dx0>>shift)&MASK;wanted[2]=(product>>32)&MASK
                count+=44 if wide else 34;groups['helper_product']+=1
        wanted[0]=value;wanted[4]=(hsp+4)&MASK
        for k,r in enumerate([5,7,6,1]):wanted[r]=get(hsp-16+4*k)
        count+=int(wide) # wide-only jump back to the shared comparison
        same=wanted[6]==wanted[0]
        groups[('wide' if wide else 'short')+('_reject' if same else '_continue')]+=1
        if same:
            wanted[0]=1
            for off,r in zip([16,20,24,28,32],[5,6,2,1,3]):wanted[r]=get(sp+off)
            wanted[4]=(sp+40)&MASK;stop=get(sp+36);count+=11
        else:stop=CODE+0x2c691;count+=2
        groups['stack_alias']+=(i//2)%6==5;groups['wrapped_stack']+=sp in [0,1,0xfffffff1]
        groups['endpoint_wrap']+=not(-2147483648<=signed(tx)+signed(tdx)<=2147483647) or not(-2147483648<=signed(lx)+signed(dx)<=2147483647)
        writes.clear();visits.clear();em.emu_start(CODE+(0x2c637 if wide else 0x2c65f),0,count=count)
        require(em.reg_read(x.UC_X86_REG_EIP)==stop,f'case {i}: wrong stop')
        require(len(visits)==count,f'case {i}: wrong count')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: wrong registers')
        require(writes==expected,f'case {i}: wrong ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: wrong data memory')
    require(all(groups.values()),'missing branch coverage')
    return {'total_cases':2048,'groups':groups,
      'checks':'Both real second-helper calls, complete helper bodies, same-side comparison and rejected callback RET. All eight registers, mapped data memory, ordered writes, instruction count and final PC; wrapping endpoints/stacks and stack aliases.',
      'scope':'Starts at first-helper return with arbitrary first result 0/1; no helper stubs. Final flags not compared. Return code addresses normalized by CODE base. Does not execute the fraction calculation or insertion path.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec,profile,raw=extracted();out=ROOT/'artifacts/original-line-second-point';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineSecondPoint'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Second point tests, production side results under explicit boundary inputs, same-side no-intercept result and real callback return, post-sound firing prefix <=541 instructions. Initial-map supply of the callback input relation, fraction calculation, insertion and whole-game equivalence remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original second-point tests, same-side rejection and firing join; byte certificates and axiom audit.')
    if args.cross_check:print('Native second-point cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise

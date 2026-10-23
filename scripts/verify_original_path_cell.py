#!/usr/bin/env python3
"""Certify DOS path-cell dispatch and line bounds, joined to first firing."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['dispatch_checked','entry_checked','return_checked','dispatch_execution_checked','bounds_execution_checked']
PROOFS=['OriginalPathCell.'+n for n in ['decoded','gate_execution','call_execution','enter_execution','resume_execution','call_inputs','call_frame','first_visit_execution','after_line_execution']]
PROOFS+=['OriginalLineBounds.'+n for n in ['decoded','entry_execution','guard_execution','return_execution','execution','entry_frame','guard_frame','entry_coordinates','dimension_int','live_bounds','live_pc','outside_return']]
PROOFS+=['E1M1PathCell.'+n for n in ['contains_prior','contains_cell','contains_bounds','flags_from_init','first_flags_from_caller','first_bounds_execution']]

def certificate(raw):
    source='''import Doom.Proofs.E1M1PathCell
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPathCell
open Doom Doom.Proofs X86 X86Memory X86Control
'''
    for name in ['dispatch','lineEntry','lineReturn']:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
    source+='''theorem dispatch_checked : dispatchBytes=OriginalPathCell.code := by decide
theorem entry_checked : lineEntryBytes=OriginalLineBounds.lineEntry := by decide
theorem return_checked : lineReturnBytes=OriginalLineBounds.lineReturn := by decide
theorem dispatch_execution_checked (line : Bool) (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤6 ∧ X86Routine.Prefix (OriginalPathCell.bytesProgram dispatchBytes) [] n
      ⟨s,f,OriginalPathCell.gatePc line⟩ (OriginalPathCell.enter line s) := by
  rw [dispatch_checked]; exact OriginalPathCell.enter_execution line s f
theorem bounds_execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤16 ∧ X86Routine.Prefix (OriginalLineBounds.bytesProgram lineEntryBytes lineReturnBytes) [] n
      ⟨s,f,0x2c520⟩ (OriginalLineBounds.result s) := by
  rw [entry_checked,return_checked]; exact OriginalLineBounds.execution s f
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathCell\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedPathCell.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected output')

def cross_check(raw,spec):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x50000)
    for name,unit in spec['units'].items():
        start=int(unit['code_offset'],16);code=bytearray(raw[name])
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
        require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
        for fixup in unit['relocations']:
            if fixup['object']==1:struct.pack_into('<I',code,fixup['offset'],CODE+int(fixup['target'],16))
        em.mem_write(CODE+start,bytes(code))
    addresses=[0,0x2c000,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2ca7f);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&((1<<(8*size))-1))))
    stop_address=[None]
    def instruction(emu,a,size,data):
        if a==stop_address[0]:emu.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,instruction)
    groups=dict(line_call=0,thing_call=0,skip=0,abort=0,resume=0,negative_x=0,negative_y=0,width=0,height=0,inside=0,wrapped=0)
    signed=lambda v:v if v<2**31 else v-2**32
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v):
            for k,b in enumerate(struct.pack('<I',v&MASK)):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(4))
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[HEAP+512,HEAP+515,0,1,0xfffffff1][i%5];rr[4]=sp
        mode='dispatch' if i<1024 else ('bounds' if i<1536 else 'resume')
        line=bool(i%2);bits=(i//2)&255
        put(sp+64,bits);put(sp,CODE+0x2ca94)
        if mode=='bounds':
            j=i-1024;w,h=17,11
            pairs=[(-1,0),(0,-1),(w,0),(0,h),(w-1,h-1),(0,0),(2**31-1,3),(-2**31,0),(3,2)]
            ax,ay=pairs[j%len(pairs)];rr[0]=ax&MASK;rr[2]=ay&MASK
            if j%19==0:w,h=0,0
            if j%23==0:w,h=0x80000000,0xffffffff
            put(0x2c0fc,w);put(0x2c110,h)
        if mode=='resume':rr[0]=[0,1,0xffffffff,0x80000000][(i//2)%4]
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|((i&1)<<6)|((i&2)<<10))
        wanted=rr.copy();expected=[]
        def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
        if mode=='dispatch':
            start=0x2ca7f if line else 0x2ca9c
            if bits&(1 if line else 2):
                wanted[0],wanted[2]=rr[6],rr[1];wanted[3]=CODE+(0x2c5f0 if line else 0x2c720)
                wanted[4]=(sp-4)&MASK;store(sp-4,CODE+(0x2ca94 if line else 0x2cab1))
                stop=0x2c520 if line else 0x2c5a0;count=6;groups['line_call' if line else 'thing_call']+=1
            else:stop=0x2ca9c if line else 0x2cab5;count=2;groups['skip']+=1
        elif mode=='resume':
            start=0x2ca94 if line else 0x2cab1;count=2
            stop=0x2cb0b if rr[0]==0 else (0x2ca9c if line else 0x2cab5)
            groups['abort' if rr[0]==0 else 'resume']+=1
        else:
            start=0x2c520;store(sp-4,rr[7]);store(sp-8,rr[3]);wanted[4]=(sp-8)&MASK
            ax,ay=signed(rr[0]),signed(rr[2]);w,h=signed(get(0x2c0fc)),signed(get(0x2c110))
            if ax<0:kind='negative_x';count=5
            elif ay<0:kind='negative_y';count=7
            else:
                wanted[3]=get(0x2c0fc)
                if ax>=w:kind='width';count=10
                elif ay>=h:kind='height';count=12
                else:kind='inside';count=12
            groups[kind]+=1
            if kind=='inside':stop=0x2c541
            else:
                wanted[0]=1;wanted[7]=get(sp-4);wanted[4]=(sp+4)&MASK
                stop=get(sp)-CODE;count+=4
        groups['wrapped']+=sp in [0,1,0xfffffff1]
        writes.clear();visits.clear();stop_address[0]=CODE+stop
        try:em.emu_start(CODE+start,CODE+stop,count=16)
        except u.UcError as error:
            raise ValueError(f'case {i} mode={mode} sp={sp:#x} pc={em.reg_read(x.UC_X86_REG_EIP):#x} visits={visits} writes={writes}: {error}') from error
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+stop,f'case {i}: wrong stop')
        require(len(visits)==count,f'case {i}: wrong count {len(visits)} vs {count}')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: wrong registers')
        require(writes==expected,f'case {i}: wrong ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: wrong data memory')
    require(all(groups.values()),'missing branch coverage')
    return {'total_cases':2048,'groups':groups,
      'checks':'all eight registers, all mapped data memory, ordered writes, instruction count and PC; all 256 low flag bytes for each gate; signed boundary and unaligned/wrapping stack cases',
      'scope':'stops at actual iterator entries, before BLOCKMAP reads, or at real return/abort destinations; no callbacks are stubbed; final flags not compared; code-pointer relocation normalized by CODE base'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-path-cell.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(1,3))
    out=ROOT/'artifacts/original-path-cell';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PathCell'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Original cell gates and real CALL/return-site tests; line bounds and successful outside epilogue; production signed bounds correspondence; firing join <=360 instructions derives line-enabled from caller. Bounds representation, caller layout, prior geometry/sound, loader/hardware and reachability obligations remain. BLOCKMAP iteration/callbacks, full traversal and whole-game equivalence are open.',
      'cross_check':cross_check(raw,spec) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original cell dispatch, line bounds and joined first firing; extracted byte certificates and axiom audit.')
    if args.cross_check:print('Native cell cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise

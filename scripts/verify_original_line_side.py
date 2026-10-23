#!/usr/bin/env python3
"""Certify complete original linedef point-side helper and its short-trace caller."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','execution_checked']
PROOFS=['OriginalLineSide.'+n for n in ['decoded','prepare_execution','diagonal_execution','finish_execution','vle_execution','vgt_execution','hle_execution','hgt_execution','compare_execution','body_execution','execution','diagonal_value','diagonal_memory','diagonal_stack','body_value','body_frame','frame','returned','live']]
PROOFS+=['E1M1LineSide.'+n for n in ['contains_prior','contains_entry','continue_execution','first_side_execution','helper_live','entry_inputs','short_result']]

def certificate(raw):
    source='''import Doom.Proofs.E1M1LineSide
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineSide
open Doom Doom.Proofs X86 X86Memory X86Control OriginalLineSide
'''
    source+='def bytes : List UInt8 := ['+','.join(hex(b) for b in raw['side'])+']\n'
    source+='''theorem bytes_checked : bytes=code := by decide
theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤34 ∧ X86Routine.Prefix (bytesProgram bytes) [] n ⟨s,f,0x2c010⟩ (result s) := by
  rw [bytes_checked]; exact execution s f
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineSide\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedLineSide.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected output')

def cross_check(raw):
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x50000)
    code=raw['side'];listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,0x2c010))
    require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
    em.mem_write(CODE+0x2c010,code)
    addresses=[0,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c010);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&((1<<(8*size))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _,a,size,data:visits.append(a-CODE))
    groups=dict(vertical_le=0,vertical_gt=0,horizontal_le=0,horizontal_gt=0,diagonal_zero=0,diagonal_one=0,
                zero_length=0,point_equal=0,product_tie=0,stack_alias=0,wrapped_stack=0)
    edges=[-2147483648,-65537,-65536,-1,0,1,65535,65536,2147483647]
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v):
            for k,b in enumerate((v&MASK).to_bytes(4,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(4))
        rr=[rng.getrandbits(32) for _ in regs]
        line,vertex=HEAP+512,HEAP+1024
        sp=[HEAP+128,HEAP+131,0,1,0xfffffff1,line+24][i%6];rr[4]=sp;rr[3]=line
        dx,dy=edges[i%9],edges[(i//9)%9]
        if i%3==0:dx=0
        elif i%3==1:dy=0
        if i>=1458 and i%3==2:dx,dy=signed(rng.getrandbits(32)),signed(rng.getrandbits(32))
        vx,vy=rng.getrandbits(32),rng.getrandbits(32)
        if i%7==0:rr[0]=vx;rr[2]=vy
        elif i%7==1:rr[0]=edges[(i//7)%9]&MASK;rr[2]=edges[(i//63)%9]&MASK
        put(line,vertex);put(vertex,vx);put(vertex+4,vy);put(line+8,dx);put(line+12,dy);put(sp,CODE+0x4f000)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|((i&1)<<6)|((i&2)<<10))
        wanted=rr.copy();expected=[]
        for k,r in enumerate([1,6,7,5],1):
            expected.append(((sp-4*k)&MASK,4,rr[r]));put(sp-4*k,rr[r])
        dx,dy=signed(get(line+8)),signed(get(line+12))
        px,py=signed(rr[0]),signed(rr[2]);vx,vy=signed(get(vertex)),signed(get(vertex+4))
        if dx==0:
            le=px<=vx;value=int(dy>0 if le else dy<0);wanted[2]=vertex;count=18
            groups['vertical_le' if le else 'vertical_gt']+=1
        elif dy==0:
            le=py<=vy;value=int(dx<0 if le else dx>0);count=20
            groups['horizontal_le' if le else 'horizontal_gt']+=1
        else:
            left=(((dy>>16)*signed((px-vx)&MASK))>>16)&MASK
            product=signed((py-vy)&MASK)*(dx>>16)
            right=(product>>16)&MASK;value=int(signed(right)>=signed(left));count=34
            wanted[3]=(dx>>16)&MASK;wanted[2]=(product>>32)&MASK
            groups['diagonal_one' if value else 'diagonal_zero']+=1;groups['product_tie']+=left==right
        wanted[0]=value;wanted[4]=(sp+4)&MASK
        groups['zero_length']+=dx==dy==0;groups['point_equal']+=px==vx and py==vy
        groups['stack_alias']+=sp==line+24;groups['wrapped_stack']+=sp in [0,1,0xfffffff1]
        writes.clear();visits.clear();em.emu_start(CODE+0x2c010,0,count=count)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x4f000,f'case {i}: wrong return')
        require(len(visits)==count,f'case {i}: wrong count')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: wrong registers')
        require(writes==expected,f'case {i}: wrong ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: wrong data memory')
    require(all(groups.values()),'missing branch coverage')
    # SETG is the only new model instruction. Check every low/high byte register
    # and every combination of the three flags it consumes, preserving all flags.
    for r in range(8):
        pc=CODE+0x49000+r*16;em.mem_write(pc,bytes([0x0f,0x9f,0xc0+r]))
        for flags in range(8):
            sf,zf,of=flags&1,(flags>>1)&1,(flags>>2)&1
            rr=[rng.getrandbits(32) for _ in regs]
            for reg,v in zip(regs,rr):em.reg_write(reg,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(sf<<7)|(zf<<6)|(of<<11))
            before=em.reg_read(x.UC_X86_REG_EFLAGS);value=int(not zf and sf==of)
            shift=0 if r<4 else 8;rr[r%4]=(rr[r%4]&~(255<<shift))|(value<<shift)
            em.emu_start(pc,0,count=1)
            require([em.reg_read(reg) for reg in regs]==rr,'SETG byte-register mismatch')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)==before,'SETG changed flags')
    return {'total_cases':2048,'setg_cases':64,'groups':groups,
      'checks':'complete helper through RET; all eight registers, mapped memory, ordered writes, instruction count and PC. Axis/diagonal signs, ties, zero-length lines, wrapped arithmetic, unaligned/wrapping stacks and stack aliases. SETG checks all eight byte registers and SF/ZF/OF combinations.',
      'scope':'helper flags are not compared; isolated SETG flags are compared. Return pointers normalized by CODE base. No helper stubs.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-line-side.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(3,))
    out=ROOT/'artifacts/original-line-side';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineSide'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Complete P_PointOnLineSide, production Line.pointSide result, restored saved registers and return; callback-to-helper input transport. Firing prefix <=435 instructions, continuing only on real linedef-helper entry. Divline helper, second point test, remaining callback/list, initialization and whole-game equivalence remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete original linedef point-side helper and short-trace caller; byte certificates and axiom audit.')
    if args.cross_check:print('Native line-side cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise

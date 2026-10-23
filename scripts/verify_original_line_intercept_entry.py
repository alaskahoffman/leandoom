#!/usr/bin/env python3
"""Certify original line-intercept entry and first point-side call."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['entry_checked','short_checked','first_checked']
PROOFS=['OriginalLineInterceptEntry.'+n for n in ['decoded','prepare_execution','gate_execution','call_execution','gate_pc','gate_preserves','first_execution','prepared_memory','prepared_regs','frame','call_inputs','call_frame','first_frame','selection_live','live']]
PROOFS+=['E1M1LineInterceptEntry.'+n for n in ['contains_prior','contains_entry','continue_execution','first_point_execution','callback_live']]

def certificate(raw):
    source='''import Doom.Proofs.E1M1LineInterceptEntry
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineInterceptEntry
open Doom Doom.Proofs X86 X86Memory X86Control OriginalLineInterceptEntry
'''
    for name in ['entry','short']:
        source+='def '+name+' : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'='+name+'Bytes := by decide\n'
    source+='''theorem first_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤22 ∧ X86Routine.Prefix (bytesProgram entry short) [] n ⟨s,f,0x2c5f0⟩ (first s) := by
  rw [entry_checked,short_checked]; exact first_execution s f
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineInterceptEntry\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedLineInterceptEntry.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
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
    for name,start in [('entry',0x2c5f0),('short',0x2c64d)]:
        code=raw[name];listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,start))
        require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
        em.mem_write(CODE+start,code)
    addresses=[0,0x2b000,HEAP,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c5f0);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&((1<<(8*size))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _,a,size,data:visits.append(a-CODE))
    groups=dict(dx_positive=0,dy_positive=0,dx_negative=0,dy_negative=0,short=0,exact_boundary=0,stack_alias=0,wrapped_stack=0)
    edges=[-2147483648,-1048577,-1048576,-1048575,-1,0,1,1048575,1048576,1048577,2147483647]
    signed=lambda v:v if v<0x80000000 else v-0x100000000
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v,size=4):
            for k,b in enumerate((v&((1<<(8*size))-1)).to_bytes(size,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(4))
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[HEAP+128,HEAP+131,0,1,0xfffffff1,0x2ba20][i%6];rr[4]=sp
        line,vertex=HEAP+513,HEAP+1027;rr[0]=line
        dx,dy=(edges[i%11],edges[(i//11)%11]) if i<1210 else (signed(rng.getrandbits(32)),signed(rng.getrandbits(32)))
        put(line,vertex);put(vertex,rng.getrandbits(32));put(vertex+4,rng.getrandbits(32))
        for a,v in [(0x2ba10,rng.getrandbits(32)),(0x2ba14,rng.getrandbits(32)),(0x2ba18,dx),(0x2ba1c,dy)]:put(a,v)
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|((i&1)<<6)|((i&2)<<10))
        wanted=rr.copy();expected=[]
        def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
        for k,r in enumerate([3,1,2,6,5],1):store(sp-4*k,rr[r])
        wanted[4]=(sp-36)&MASK;wanted[1]=line;wanted[2]=get(0x2ba18)
        dx=signed(wanted[2]);dy=signed(get(0x2ba1c))
        if dx>1048576:branch='dx_positive';count=2
        else:
            wanted[3]=get(0x2ba1c)
            if dy>1048576:branch='dy_positive';count=5
            elif dx< -1048576:branch='dx_negative';count=7
            elif dy< -1048576:branch='dy_negative';count=9
            else:branch='short';count=9
        wide=branch!='short';groups[branch]+=1
        groups['exact_boundary']+=abs(dx)==1048576 or abs(dy)==1048576
        groups['stack_alias']+=sp==0x2ba20;groups['wrapped_stack']+=sp in [0,1,0xfffffff1]
        if wide:
            vp=get(line);wanted[0]=get(vp);wanted[2]=get(vp+4);wanted[3]=0x2ba10
        else:wanted[0]=get(0x2ba10);wanted[2]=get(0x2ba14);wanted[3]=line
        ret=0x2c637 if wide else 0x2c65f;stop=0x2c1e0 if wide else 0x2c010
        store(sp-40,CODE+ret);wanted[4]=(sp-40)&MASK;count+=8+(5 if wide else 4)
        writes.clear();visits.clear();em.emu_start(CODE+0x2c5f0,0,count=count)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+stop,f'case {i}: wrong stop')
        require(len(visits)==count,f'case {i}: wrong count')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: wrong registers')
        require(writes==expected,f'case {i}: wrong ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: wrong data memory')
    require(all(groups.values()),'missing branch coverage')
    return {'total_cases':2048,'groups':groups,
      'checks':'all eight registers, all mapped data memory, ordered writes, exact instruction counts and final PC; all five selection branches, strict boundaries, unaligned/wrapping stacks and stack writes aliasing trace globals',
      'scope':'stops at first real point-side helper entry; no helper stubs. Final flags not compared. Code and return pointers normalized by CODE base.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-line-intercept-entry.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(3,))
    out=ROOT/'artifacts/original-line-intercept-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineInterceptEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Original line callback prologue, strict side-test selection and first helper arguments. Firing prefix <=401 instructions, conditional on actual callback entry. Helper bodies, second point test, remaining callback/list, initialization and whole-game equivalence remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original line-intercept selection, first helper call and joined firing; byte certificates and axiom audit.')
    if args.cross_check:print('Native line-intercept-entry cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise

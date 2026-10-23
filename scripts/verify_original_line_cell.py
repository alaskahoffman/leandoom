#!/usr/bin/env python3
"""Certify the original BLOCKMAP lookup and one line-list iteration."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','lookup_checked','visit_checked','first_checked']
PROOFS=['OriginalLineCell.'+n for n in ['decoded','lookup_execution','header_execution','duplicate_execution','callback_execution','advance_execution','resume_execution','sentinel','lookup_observe','header_pc','natural_bits','live_index','short_nonnegative','live_lookup','callback_observe','callback_frame','skip_observe','visit_execution','first_execution']]
PROOFS+=['E1M1LineCell.'+n for n in ['contains_prior','contains_cell','continue_execution','first_cell_execution','inside_state','bounds_to_lookup']]

def certificate(raw):
    source='''import Doom.Proofs.E1M1LineCell
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineCell
open Doom Doom.Proofs X86 X86Memory X86Control OriginalLineCell
'''
    source+='def bytes : List UInt8 := ['+','.join(hex(b) for b in raw['cell'])+']\n'
    source+='''theorem bytes_checked : bytes=code := by decide
theorem lookup_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram bytes) [] 8 ⟨s,f,0x2c541⟩ (lookup s) := by
  rw [bytes_checked]; exact lookup_execution s f
theorem visit_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤11 ∧ X86Routine.Prefix (bytesProgram bytes) [] n ⟨s,f,0x2c57f⟩ (visit s) := by
  rw [bytes_checked]; exact visit_execution s f
theorem first_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤19 ∧ X86Routine.Prefix (bytesProgram bytes) [] n ⟨s,f,0x2c541⟩ (first s) := by
  rw [bytes_checked]; exact first_execution s f
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineCell\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedLineCell.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
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
    code=raw['cell'];listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,0x2c541))
    require(b''.join(bytes(i.bytes) for i in listing)==code,'decoder mismatch')
    em.mem_write(CODE+0x2c541,code)
    addresses=[0,0x13000,0x2c000,HEAP,HEAP+4096,0xfffff000]
    for a in addresses:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c541);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _,access,a,size,value,data:writes.append((a&MASK,size,value&((1<<(8*size))-1))))
    def instruction(emu,a,size,data):
        visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,instruction)
    groups=dict(sentinel=0,duplicate=0,fresh=0,leading_zero=0,negative_offset=0,negative_id=0,
                mark_alias_callback=0,mark_alias_return=0,abort=0,resume=0,wrapped_stack=0)
    sx16=lambda v:v if v<0x8000 else v-0x10000
    for i in range(2048):
        pages={a:bytearray(rng.randbytes(4096)) for a in addresses}
        def put(a,v,size=4):
            for k,b in enumerate((v&((1<<(8*size))-1)).to_bytes(size,'little')):
                q=(a+k)&MASK;pages[q&~4095][q&4095]=b
        def get(a,size=4):return sum(pages[((a+k)&MASK)&~4095][((a+k)&MASK)&4095]<<(8*k) for k in range(size))
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[HEAP+128,HEAP+131,0,1,0xfffffff1][i%5];rr[4]=sp
        mode='first' if i<1024 else ('visit' if i<1792 else 'resume')
        listptr=HEAP+1025;offset=[0,1,32767,32768,65535][i%5]
        ident=[65535,0,1,32767,32768,65534][i%6]
        mark=HEAP+4096+513
        if i%17==0:mark=sp;groups['mark_alias_callback']+=mode!='resume'
        elif i%19==0:mark=(sp-4)&MASK;groups['mark_alias_return']+=mode!='resume'
        addr=(mark-54)&MASK
        epoch=(CODE+0x2c600) if mark==sp else rng.getrandbits(32)
        put(sp,CODE+0x2c5f0)
        put(0x13580,epoch);put(0x2c120,addr-sx16(ident)*62)
        put(mark,epoch if (i//6)%2==0 else epoch^0x12345678)
        put(listptr,ident,2)
        if mode=='first':
            index=(rr[0]+rr[2]*rr[3])&MASK
            put(0x2c100,HEAP+769-((index*2)&MASK));put(HEAP+769,offset,2)
            put(0x2c10c,listptr-sx16(offset)*2)
            groups['negative_offset']+=offset>=32768
        elif mode=='visit':rr[2]=listptr
        else:rr[0]=[0,1,0xffffffff,0x80000000][i%4]
        for a,page in pages.items():em.mem_write(a,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|((i&1)<<6)|((i&2)<<10))
        wanted=rr.copy();expected=[]
        def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
        if mode=='resume':
            start=0x2c578;count=2;stop=0x2c58c if rr[0]==0 else 0x2c57c
            groups['abort' if rr[0]==0 else 'resume']+=1
        else:
            start=0x2c541 if mode=='first' else 0x2c57f;count=8 if mode=='first' else 0
            wanted[2]=listptr;wanted[0]=sx16(ident)&MASK;count+=3
            groups['leading_zero']+=ident==0;groups['negative_id']+=32768<=ident<65535
            if ident==65535:stop=0x2c587;groups['sentinel']+=1
            else:
                wanted[0]=addr;wanted[3]=get(0x2c120);wanted[7]=get(0x13580);count+=6
                if wanted[7]==get(mark):
                    groups['duplicate']+=1;wanted[2]=(listptr+2)&MASK;stop=0x2c57f;count+=1
                else:
                    groups['fresh']+=1;store(mark,wanted[7])
                    # The indirect target is read AFTER the stamp, BEFORE the push.
                    stop=get(sp)-CODE;store(sp-4,CODE+0x2c578);wanted[4]=(sp-4)&MASK;count+=2
        groups['wrapped_stack']+=sp in [0,1,0xfffffff1]
        writes.clear();visits.clear()
        # Bound the prefix by its independently predicted instruction count:
        # duplicate processing legitimately ends at the starting header PC.
        em.emu_start(CODE+start,0,count=count)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+stop,f'case {i}: wrong stop')
        require(len(visits)==count,f'case {i}: wrong count')
        require([em.reg_read(r) for r in regs]==wanted,f'case {i}: wrong registers')
        require(writes==expected,f'case {i}: wrong ordered writes')
        for a,page in pages.items():require(em.mem_read(a,4096)==page,f'case {i}: wrong data memory')
    require(all(groups.values()),'missing branch coverage')
    return {'total_cases':2048,'groups':groups,
      'checks':'all eight registers, all mapped data memory, ordered writes, exact instruction counts and final PC; signed offsets/ids, leading zero, sentinel, duplicate, new stamp, callback/return alias cases and unaligned/wrapping stacks',
      'scope':'one list item, stops before callback execution; no callback stubs. Negative offsets/ids test the machine model outside the accepted production profile. Final flags not compared; callback and return code pointers normalized by CODE base.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-line-cell.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(3,))
    out=ROOT/'artifacts/original-line-cell';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineCell'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout);(out/'axioms.log').write_text(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':checked.stdout.splitlines(),
      'scope':'Cell lookup plus one signed list item, sentinel, duplicate skip or mark-before-indirect-call; callback return gate. Firing prefix <=379 instructions. Bounds-to-lookup transports encoded map reads. Full list iteration, callback behavior, map initialization/reachability and whole-game equivalence remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original BLOCKMAP lookup, line-list item and joined firing; byte certificates and axiom audit.')
    if args.cross_check:print('Native line-cell cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:print(error.stdout or '');print(error.stderr or '');raise

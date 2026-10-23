#!/usr/bin/env python3
"""Certify the owned-allocation branch and the free remainder it establishes."""
import argparse
import json
import re
import subprocess
import verify_original_group_heap as heap

ROOT, require = heap.ROOT, heap.require
NS = 'Doom.Verification.ExtractedGroupRemainder.'
NAMES = heap.NAMES + [NS+n for n in ['owned_checked','split_owned_checked','view_checked']]
for module,names in [
    ('HeapWrites',['frame','assigned','append']),
    ('OriginalGroupOwned',['decoded','execution','frame']),
    ('OriginalGroupRemainder',['split_memory','split_register','published_memory','published_reads',
                               'result_memory','establishes_view','owner_published','execution'])]:
    NAMES += ['Doom.Proofs.'+module+'.'+n for n in names]


def certificate(raw):
    source = heap.certificate(raw).replace('import Doom.Proofs.OriginalGroupHeap',
                                         'import Doom.Proofs.OriginalGroupRemainder')
    source += '''namespace Doom.Verification.ExtractedGroupRemainder
open X86 X86Memory X86Control Doom.Proofs

theorem owned_checked (s : X86Memory.State) (f : Option Flags) (user : s.regs 7≠(0#32)) :
    X86Routine.run (OriginalGroupAllocation.bytesProgram ExtractedGroupHandoff.allocation)
      [0x39771] 12 ⟨s,f,0x39731⟩=some (OriginalGroupOwned.result s) := by
  rw [ExtractedGroupHandoff.allocation_bytes]
  exact OriginalGroupOwned.execution s f user

theorem split_owned_checked (p : OriginalGroupRemainder.Plan) (s : X86Memory.State)
    (f : Option Flags) (user : p.owner≠0) :
    X86Routine.run ExtractedGroupSelected.program [0x39771] 26
      ⟨p.input s,f,0x39704⟩=some (p.result s) := by
  rw [ExtractedGroupSelected.program_checked]
  exact OriginalGroupRemainder.execution p s f user

theorem view_checked (p : OriginalGroupRemainder.Plan) (s : X86Memory.State)
    (conditions : OriginalGroupRemainder.Conditions p s.memory) :
    p.view.Holds (p.result s).core.memory :=
  OriginalGroupRemainder.establishes_view p s conditions
'''
    source += '\n'.join('#print axioms '+n for n in NAMES[len(heap.NAMES):])
    return source+'\nend Doom.Verification.ExtractedGroupRemainder\n'


def audit(output):
    rest = output.strip()
    for name in NAMES:
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw):
    import random
    import struct
    import unicorn as uc
    from unicorn import x86_const as x
    rng = random.Random(0x39735)
    regs = [x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    cases = 0
    for align in range(4):
      for request in [28,928,2592]:
       for excess in [65,128,6444536]:
        for tag in [50,101]:
         for high in [False,True]:
            em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
            code = 0x100000
            em.mem_map(code,0x40000)
            em.mem_write(code+0x396f8,raw['select_split'])
            em.mem_write(code+0x39731,raw['allocation'])
            regions = [(0,0x80000),(0x610000,0x1000),(0x620000,0x3000),
                       (0x630000,0x1000),(0xfffff000,0x1000)]
            memory = {}
            for base,size in regions:
                em.mem_map(base,size); memory[base]=bytearray(size)
            def write(a,v):
                for base,buf in memory.items():
                    if base<=a and a+4<=base+len(buf):
                        struct.pack_into('<I',buf,a-base,v&0xffffffff);return
                raise ValueError('unmapped write '+hex(a))
            zone=0x610000+align;block=0x620000+align;after=0x622000+align
            owner=(0xfffff010 if high else 0x630010)+align
            remainder=block+request
            write(0x74fe0,zone);write(block+16,after)
            for base,buf in memory.items():em.mem_write(base,bytes(buf))
            initial=[rng.getrandbits(32) for _ in regs]
            initial[0]=request+excess;initial[1]=request;initial[3]=block;initial[5]=tag;initial[7]=owner
            for r,v in zip(regs,initial):em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x202)
            writes=[(remainder+4,0),(remainder+8,0),(remainder,excess),(remainder+20,block),
                    (remainder+16,after),(after+20,remainder),(block+16,remainder),(block,request),
                    (block+4,owner),(owner,block+24),(block+8,tag),(zone+28,remainder),(block+12,0x1d4a11)]
            for a,v in writes:write(a,v)
            seen=[];pcs=[]
            em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_k,a,n,v,_u:seen.append((a,n,v&0xffffffff)))
            em.hook_add(uc.UC_HOOK_CODE,lambda _e,a,_n,_u:pcs.append(a-code))
            em.emu_start(code+0x39704,code+0x39771,count=27)
            expected=initial.copy();expected[0]=block+24;expected[2]=zone
            require(em.reg_read(x.UC_X86_REG_EIP)==code+0x39771,'wrong exit')
            require(len(pcs)==26,'wrong instruction count')
            require([em.reg_read(r) for r in regs]==expected,'register mismatch')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==(0x80 if high else 0),'modeled flag mismatch')
            require(seen==[(a,4,v) for a,v in writes],'ordered writes differ')
            for base,buf in memory.items():require(bytes(em.mem_read(base,len(buf)))==bytes(buf),'memory differs')
            cases+=1
    return dict(cases=cases,comparisons=['registers','modeled flags','ordered writes','mapped data memory','exit','instruction count'],
                scope='Split decision through nonzero-owner metadata commit. Stops before register restoration and RET. Synthetic initial RAM, not startup reachability.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    raw,profile,_=heap.malloc.extracted()
    out=ROOT/'artifacts/original-group-remainder';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupRemainder'],cwd=ROOT,
                       stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,
                          capture_output=True,text=True,timeout=90)
    if result.returncode:print(result.stdout);print(result.stderr);result.check_returncode()
    audit(result.stdout);require(not result.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],
        audited_declarations=len(NAMES),axioms=result.stdout.splitlines(),cross_check=native,
        scope='Nonzero-owner metadata branch and split-remainder header establishment. '
              'Earlier heap state, allocation entry, return/caller seam and startup ordering remain open.'),indent=2)+'\n')
    print(result.stdout,end='')
    print('PASS: split and cache-owner publication establish the following free-block view.')


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify owned-allocation restoration, RET, and the caller's W_ReadLump CALL."""
import argparse
import json
import re
import subprocess
import verify_original_group_remainder as prior
ROOT, require = prior.ROOT, prior.require
NS = 'Doom.Verification.ExtractedGroupReturn.'
NAMES = prior.NAMES + [NS+n for n in ['cache_bytes','program_checked','execution_checked']]
for module,names in [
    ('OriginalGroupRestore',['decoded','execution','memory','registers']),
    ('OriginalGroupCacheCall',['decoded','execution','arguments','return_address','frame']),
    ('OriginalGroupReturn',['saved_frame','metadata_stack','return_pc','restored_registers','returned_view',
                            'return_execution','cache_agrees','allocator_agrees','execution','read_arguments',
                            'read_return','read_view'])]:
    NAMES += ['Doom.Proofs.'+module+'.'+n for n in names]


def certificate(raw):
    source = prior.certificate(raw).replace('import Doom.Proofs.OriginalGroupRemainder',
                                           'import Doom.Proofs.OriginalGroupReturn')
    source += 'namespace Doom.Verification.ExtractedGroupReturn\nopen X86 X86Memory X86Control Doom.Proofs\n'
    source += 'def cacheBytes : List UInt8 := ['+','.join(hex(b) for b in raw['cache_call'])+']\n'
    source += """theorem cache_bytes : cacheBytes=OriginalGroupCacheCall.cacheBytes := by decide +kernel

def program : X86Routine.Program := fun pc =>
  if 0x38d41≤pc ∧ pc<0x38d50 then OriginalGroupCacheCall.bytesProgram cacheBytes pc
  else ExtractedGroupSelected.program pc

theorem program_checked : program=OriginalGroupReturn.program := by
  unfold program
  rw [cache_bytes,ExtractedGroupSelected.program_checked]
  rfl

theorem execution_checked (p : OriginalGroupRemainder.Plan) (s : X86Memory.State) (f : Option Flags)
    (c : OriginalGroupRemainder.Conditions p s.memory) (safe : OriginalGroupReturn.FrameSafe p s)
    (ret : load32 s.memory (s.regs 4+16)=0x38d41) :
    X86Routine.run program [0x38bf0] 35 ⟨p.input s,f,0x39704⟩=some (OriginalGroupReturn.result p s) := by
  rw [program_checked]
  exact OriginalGroupReturn.execution p s f c safe ret
"""
    source += '\n'.join('#print axioms '+n for n in NAMES[len(prior.NAMES):])
    return source+'\nend Doom.Verification.ExtractedGroupReturn\n'


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
         for high,wrapping in [(h,w) for h in [False,True] for w in [False,True]]:
            em = uc.Uc(uc.UC_ARCH_X86,uc.UC_MODE_32)
            code = 0x100000
            em.mem_map(code,0x40000)
            em.mem_write(code+0x396f8,raw['select_split'])
            em.mem_write(code+0x39731,raw['allocation'])
            em.mem_write(code+0x38d41,raw['cache_call'])
            regions = [(0,0x80000),(0x610000,0x1000),(0x620000,0x3000),
                       (0x630000,0x1000),(0x680000,0x2000),(0xfffff000,0x1000)]
            memory = {}
            for base,size in regions:
                em.mem_map(base,size); memory[base]=bytearray(size)
            def write(a,v):
                for i in range(4):
                    at=(a+i)&0xffffffff
                    for base,buf in memory.items():
                        if base<=at<base+len(buf):
                            buf[at-base]=(v>>(8*i))&255;break
                    else:raise ValueError('unmapped write '+hex(at))
            zone=0x610000+align;block=0x620000+align;after=0x622000+align
            owner=(0xfffff010 if high else 0x630010)+align
            remainder=block+request
            sp=(0xfffffff0 if wrapping else 0x680000)+align
            write(0x74fe0,zone);write(block+16,after);write(0x74f94,(owner-60)&0xffffffff)
            for off,val in [(0,0x11111111),(4,0x22222222),(8,60),(12,15),(16,code+0x38d41)]:write(sp+off,val)
            for base,buf in memory.items():em.mem_write(base,bytes(buf))
            initial=[rng.getrandbits(32) for _ in regs]
            initial[0]=request+excess;initial[1]=request;initial[3]=block;initial[5]=tag;initial[7]=owner;initial[4]=sp
            for r,v in zip(regs,initial):em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x202)
            writes=[(remainder+4,0),(remainder+8,0),(remainder,excess),(remainder+20,block),
                    (remainder+16,after),(after+20,remainder),(block+16,remainder),(block,request),
                    (block+4,owner),(owner,block+24),(block+8,tag),(zone+28,remainder),(block+12,0x1d4a11),((sp+16)&0xffffffff,code+0x38d50)]
            for a,v in writes:write(a,v)
            seen=[];pcs=[]
            em.hook_add(uc.UC_HOOK_MEM_WRITE,lambda _e,_k,a,n,v,_u:seen.append((a,n,v&0xffffffff)))
            em.hook_add(uc.UC_HOOK_CODE,lambda _e,a,_n,_u:pcs.append(a-code))
            em.emu_start(code+0x39704,code+0x38bf0,count=36)
            expected=initial.copy();expected[0]=15;expected[1]=15;expected[2]=block+24
            expected[4]=(sp+16)&0xffffffff;expected[5]=0x11111111;expected[6]=60;expected[7]=0x22222222
            require(em.reg_read(x.UC_X86_REG_EIP)==code+0x38bf0,'wrong exit')
            require(len(pcs)==35,'wrong instruction count')
            require([em.reg_read(r) for r in regs]==expected,'register mismatch')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==(0x80 if high else 0),'modeled flag mismatch')
            require(seen==[(a,4,v) for a,v in writes],'ordered writes differ')
            for base,buf in memory.items():require(bytes(em.mem_read(base,len(buf)))==bytes(buf),'memory differs')
            cases+=1
    return dict(cases=cases,comparisons=['registers','modeled flags','ordered writes','mapped data memory','exit','instruction count'],
                scope='Split decision through owner commit, four POPs, actual RET and caller CALL into W_ReadLump. Includes ordinary/wrapping stacks and slot reuse; no file I/O or startup reachability.')


def extracted():
    raw,profile,_=prior.heap.malloc.extracted()
    extraction=prior.heap.malloc.extraction
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    spec=json.loads((ROOT/'tests/reference/original-group-return.json').read_text())
    raw.update(extraction.extract(binary,profile,spec))
    return raw,profile,spec


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    raw,profile,spec=extracted()
    out=ROOT/'artifacts/original-group-return';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupReturn'],cwd=ROOT,
                       stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,
                          capture_output=True,text=True,timeout=90)
    if result.returncode:print(result.stdout);print(result.stderr);result.check_returncode()
    audit(result.stdout);require(not result.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],
        audited_declarations=len(NAMES),axioms=result.stdout.splitlines(),cross_check=native,
        scope=spec['scope']),indent=2)+'\n')
    print(result.stdout,end='')
    print('PASS: owned allocation returns to cache caller and enters W_ReadLump with preserved heap view.')


if __name__=='__main__':main()

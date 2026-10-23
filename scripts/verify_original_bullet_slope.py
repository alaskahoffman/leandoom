#!/usr/bin/env python3
"""Pin P_BulletSlope and certify its controller; geometry calls remain explicit."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','first_checked','decision_checked','retry_checked']
PROOFS=['OriginalBulletSlope.'+n for n in ['decoded','first_execution','decision_execution','retry_execution','last_store_execution','finish_execution','initial_angle','first_arguments','retry_arguments']]
PROOFS+=['BulletAim.'+n for n in ['live_unfold','selection_slope','live_center','live_right','live_left','live_miss','facing']]
PROOFS+=['E1M1BulletAim.'+n for n in ['first_query_execution','first_query_request','accepted_execution','next_query_execution','last_execution','retry_angles','center_correspondence','right_correspondence','last_correspondence']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1BulletAim
namespace Doom.Verification.ExtractedBulletSlope
open Doom Doom.Proofs X86 X86Memory X86Control OriginalBulletSlope
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(b) for b in raw['slope'])+']\n'
    s+='''theorem bytes_checked : extracted=code := by decide
 theorem first_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram extracted) [] 9 ⟨s,f,0x2d7c0⟩ (firstCall s f) := by
  rw [bytes_checked]; exact first_execution s f
 theorem decision_checked (second : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram extracted) [] 4
      ⟨s,f,if second then 0x2d7f8 else 0x2d7d5⟩ (decision second s) := by
  rw [bytes_checked]; exact decision_execution second s f
 theorem retry_checked (second : Bool) (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram extracted) [] (if second then 4 else 5)
      ⟨s,f,if second then 0x2d807 else 0x2d7e4⟩ (retryState second s f) := by
  rw [bytes_checked]; exact retry_execution second s f
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedBulletSlope\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedBulletSlope.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
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
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    CODE,HEAP,MASK=0x100000,0x600000,0xffffffff
    for base,size in [(CODE,0x40000),(0,4096),(0x2b000,0x2000),(HEAP,4096),(0xfffff000,4096)]:em.mem_map(base,size)
    em.mem_write(CODE+0x2d7c0,raw['slope'])
    # Deliberately synthetic traversal: caller control, not map geometry, is under test.
    em.mem_write(CODE+0x2bb80,b'\xc3')
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['slope'],0x2d7c0))
    require(b''.join(bytes(i.bytes) for i in listing)==raw['slope'],'decoder left bytes')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2d7c0);writes=[];calls=[];visits=[]
    replies=[];targets=[]
    def visit(e,a,_n,_d):
        if a==CODE+0x334a9:e.emu_stop();return
        visits.append(a-CODE)
        if a==CODE+0x2bb80:
            k=len(calls)
            require(k<3,'fourth query')
            calls.append((e.reg_read(regs[0]),e.reg_read(regs[2]),e.reg_read(regs[3])))
            e.reg_write(regs[0],replies[k]);e.reg_write(regs[2],rng.getrandbits(32));e.reg_write(regs[3],rng.getrandbits(32))
            e.mem_write(0x2b9f8,struct.pack('<I',targets[k]))
            e.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
    em.hook_add(u.UC_HOOK_CODE,visit)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    groups={}
    for outcome in range(4):
        for case in range(256):
            pages={a:bytearray(rng.randbytes(4096)) for a in [0,0x2b000,0x2c000,HEAP,0xfffff000]}
            def put(a,v):
                for j,b in enumerate(struct.pack('<I',v&MASK)):
                    z=(a+j)&MASK;pages[z&~4095][z&4095]=b
            obj=HEAP+64+case%4;sp=[HEAP+3000+case%4,1,0xfffffffd][case%3]
            angle=[0,0xffffffff,0x03ffffff,0x04000000,0xfc000000,0x80000000,rng.getrandbits(32)][case%7]
            rr=[rng.getrandbits(32) for _ in regs];rr[0]=obj;rr[4]=sp
            put(obj+32,angle);put(sp,CODE+0x334a9)
            replies=[rng.getrandbits(32) for _ in range(3)]
            targets=[0,0,0]
            if outcome<3:targets[outcome]=[1,0x80000000,0xffffffff][case%3]
            count=outcome+1 if outcome<3 else 3
            # Includes zero-slope hits and nonzero-slope misses: test target-based branching.
            if case%2==0:replies[count-1]=0
            for a,b in pages.items():em.mem_write(a,bytes(b))
            for r,v in zip(regs,rr):em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
            expected=[]
            def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
            for off,r in [(4,3),(8,1),(12,2),(16,6)]:store(sp-off,rr[r])
            for k in range(count):
                store(sp-20,CODE+[0x2d7d5,0x2d7f8,0x2d819][k]);put(0x2b9f8,targets[k]);store(0x2c0c0,replies[k])
            want=[(obj,(angle+off)&MASK,0x04000000) for off in [0,0x04000000,0xfc000000][:count]]
            rr[0]=replies[count-1];rr[4]=(sp+4)&MASK
            writes.clear();calls.clear();visits.clear()
            em.emu_start(CODE+0x2d7c0,CODE+0x40000,count=40)
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x334a9,'wrong return')
            require(calls==want,'wrong ordered geometry calls')
            require([em.reg_read(r) for r in regs]==rr,'wrong restored registers')
            require(writes==expected,'wrong write order')
            for a,b in pages.items():require(em.mem_read(a,4096)==b,'wrong mapped memory')
        groups[['center','right','left','all_miss'][outcome]]={'cases':256,'queries':count,'controller_instructions':len(visits)-count}
    return {'total_cases':1024,'groups':groups,'geometry':'synthetic responses; P_AimLineAttack not executed or verified',
            'checks':'ordered arguments, target-based early exit, arbitrary slopes, registers, all data memory, writes, actual RET',
            'flags':'not compared; geometry stub deliberately clobbers flags'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-bullet-slope.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-bullet-slope';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1BulletAim'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);(out/'axioms.log').write_text(result.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
            'scope':'Original autoaim controller blocks and production three-query policy. Firing path joined through first geometry CALL. Returned target/slope correspondence and geometry execution remain explicit obligations.',
            'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original controller bytes, production policy, kernel certificates and axiom audit.')
    if args.cross_check:print('Synthetic-geometry controller cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:print(e.stdout or '');print(e.stderr or '');raise

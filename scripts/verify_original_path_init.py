#!/usr/bin/env python3
"""Pin and certify P_PathTraverse initialization through the first block stepping comparison."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','execution_checked']
PROOFS=['OriginalPathInit.'+n for n in ['decoded','execution','frame15','stored_4','stored_6','loaded_origins','live_nudge','nudges','ready']]
PROOFS+=['E1M1PathInit.'+n for n in ['first_path_execution','query_path_execution','first_path_correspondence','inputs_from_setup','first_aim_path_correspondence']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1PathInit
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedPathInit
open Doom Doom.Proofs X86 X86Memory X86Control OriginalPathInit
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(b) for b in raw['init'])+']\n'
    s+='''theorem bytes_checked : extracted=code := by decide
 theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤60 ∧ X86Routine.Prefix (bytesProgram extracted) [] n ⟨s,f,0x2c8a0⟩ (result s) := by
  rw [bytes_checked]; exact execution s f
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathInit\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedPathInit.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
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
    bases=[0,0x13000,0x2b000,0x2c000,HEAP,0xfffff000]
    em.mem_map(CODE,0x40000)
    for a in bases:em.mem_map(a,4096)
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['init'],0x2c8a0))
    require(len(listing)==60 and b''.join(bytes(i.bytes) for i in listing)==raw['init'],'decoder mismatch')
    em.mem_write(CODE+0x2c8a0,raw['init'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c8a0);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    def sar(v,n):return ((v if v<0x80000000 else v-(1<<32))>>n)&MASK
    groups={};branches={str((a,b)):0 for a in (False,True) for b in (False,True)}
    for overlap in [False,True]:
      for i in range(512):
        pages={a:bytearray(rng.randbytes(4096)) for a in bases}
        def put(a,v):
            for j,b in enumerate(struct.pack('<I',v&MASK)):
                q=(a+j)&MASK;pages[q&~4095][q&4095]=b
        def read(a):
            return int.from_bytes(bytes(pages[((a+j)&MASK)&~4095][((a+j)&MASK)&4095] for j in range(4)),'little')
        rr=[rng.getrandbits(32) for _ in regs]
        sp=([0x2c108,0x2c03c,0x2ba48,0x1358c,0x2c140][i%5] if overlap else [HEAP+3000+i%4,1,0xfffffffd][i%3])
        rr[4]=sp
        ox,oy=rng.getrandbits(32),rng.getrandbits(32)
        # Four branch quadrants, with positive/negative grid indices and wrapping origins.
        rr[0]=(ox+((i-256)<<23)+(i&1))&MASK
        rr[2]=(oy+((256-i)<<23)+((i>>1)&1))&MASK
        rr[3]=[0,0x7fffffff,0x80000000,0xffffffff,rng.getrandbits(32)][i%5]
        put(0x2c104,ox);put(0x2c108,oy)
        put(0x13580,[0,1,0xffffffff,0x7fffffff][i%4]);put(sp+4,i%8)
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        expected=[]
        def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
        store(sp-4,rr[6]);store(sp-8,rr[7]);store(sp-12,rr[5])
        arg=read(sp+4);old=read(0x13580)
        store(0x2c028,0x2ba20);ox0=read(0x2c104)
        store(0x2c024,arg&4);store(0x13580,old+1)
        bx=((rr[0]-ox0)&0x7fffff)==0
        sx=(rr[0]+(0x10000 if bx else 0))&MASK
        oy0=read(0x2c108);by=((rr[2]-oy0)&0x7fffff)==0
        sy=(rr[2]+(0x10000 if by else 0))&MASK
        oy1=read(0x2c108);ox1=read(0x2c104)
        store(0x2ba18,rr[3]-sx);store(0x2ba10,sx)
        store(0x2ba14,sy);store(0x2ba1c,rr[1]-sy)
        ox2=read(0x2c104)
        ex=(rr[3]-ox1)&MASK;rx=(sx-ox2)&MASK
        ey=(rr[1]-oy1)&MASK;ry=(sy-oy1)&MASK
        store(sp-48,sar(rx,23));store(sp-44,sar(ry,23))
        store(sp-40,sar(ex,23));fraction=sar(rx,7)&65535
        store(sp-52,fraction);store(sp-36,sar(ey,23))
        wanted=[sar(ey,23),ey,(ey-ry)&MASK,fraction,(sp-60)&MASK,ex,rx,ry]
        writes.clear();visits.clear()
        em.emu_start(CODE+0x2c8a0,CODE+0x2c96c,count=60)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2c96c,'wrong stop')
        require(len(visits)==58+bx+by,'wrong instruction count')
        require((0x2c8e1 in visits)==bx and (0x2c8f8 in visits)==by,'wrong nudge branch')
        require([em.reg_read(r) for r in regs]==wanted,'wrong registers')
        require(writes==expected,'wrong write order')
        for a,b in pages.items():require(em.mem_read(a,4096)==b,'wrong mapped data memory')
        branches[str((bx,by))]+=1
      groups['overlapping' if overlap else 'separated']={'cases':512}
    require(all(branches.values()),'missing branch quadrant')
    return {'total_cases':1024,'groups':groups,'branches':branches,
      'checks':'all registers, all mapped data memory, 15-store order, both nudge branches, signed shifts, overflow, unaligned/wrapping stacks, aliased globals',
      'scope':'stops before grid stepping, division and intercept collection; flags not compared'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-path-init.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(3,))
    out=ROOT/'artifacts/original-path-init';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1PathInit'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);(out/'axioms.log').write_text(result.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
      'scope':'58-60 instructions through path initialization, reusable query prefix <=96, firing prefix <=223. Production trace and block-coordinate correspondence requires encoded inputs and byte separation. Grid stepping, traversal, callbacks, return frame, loader and reachable-state invariant remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original path initialization, firing/query joins, kernel certificates and axiom audit.')
    if args.cross_check:print('Native path initialization cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:print(e.stdout or '');print(e.stderr or '');raise

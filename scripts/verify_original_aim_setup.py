#!/usr/bin/env python3
"""Pin and certify aim-query setup through the real P_PathTraverse CALL."""
import argparse
import json
import random
import re
import struct
import subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','execution_checked']
PROOFS=['OriginalAimSetup.'+n for n in ['decoded','execution','registers','memory','frame9','stored_return','shooter_reads','live_coordinates','live_height','live_globals','call_frame','ready']]
PROOFS+=['E1M1AimSetup.'+n for n in ['first_traversal_execution','query_setup_execution','inputs_from_ray','final_miss_execution','first_traversal_correspondence']]

def certificate(raw):
    s='''import Doom.Proofs.E1M1AimSetup
namespace Doom.Verification.ExtractedAimSetup
open Doom Doom.Proofs X86 X86Memory X86Control OriginalAimSetup
'''
    s+='def extracted : List UInt8 := ['+','.join(hex(b) for b in raw['setup'])+']\n'
    s+='''theorem bytes_checked : extracted=code := by decide
 theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix (bytesProgram extracted) [] 25 ⟨s,f,0x2bba0⟩ (traversal s) := by
  rw [bytes_checked]; exact execution s f
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join('#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedAimSetup\n'

def audit(output):
    rest=output.strip()
    for name in ['Doom.Verification.ExtractedAimSetup.'+n for n in NAMES]+['Doom.Proofs.'+n for n in PROOFS]:
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
    bases=[0,0x2b000,0x2c000,HEAP,0xfffff000]
    em.mem_map(CODE,0x40000)
    for a in bases:em.mem_map(a,4096)
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['setup'],0x2bba0))
    require(len(listing)==25 and b''.join(bytes(i.bytes) for i in listing)==raw['setup'],'decoder mismatch')
    code=bytearray(raw['setup'])
    # LE object-1 callback fixup. Data object is based at zero in this diagnostic.
    require(struct.unpack_from('<I',code,1)[0]==0x2b760,'unexpected callback')
    struct.pack_into('<I',code,1,CODE+0x2b760)
    em.mem_write(CODE+0x2bba0,bytes(code))
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2bba0);writes=[];visits=[]
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&MASK)))
    groups={}
    for overlap in [False,True]:
      for i in range(512):
        pages={a:bytearray(rng.randbytes(4096)) for a in bases}
        def put(a,v):
            for j,b in enumerate(struct.pack('<I',v&MASK)):
                q=(a+j)&MASK;pages[q&~4095][q&4095]=b
        def read(a):
            return int.from_bytes(bytes(pages[((a+j)&MASK)&~4095][((a+j)&MASK)&4095] for j in range(4)),'little')
        rr=[rng.getrandbits(32) for _ in regs]
        obj=([0x2b9a0,0x2b9a4,0x2b9a8,0x2c1c4,0xfffffff1][i%5] if overlap else HEAP+65+i%4)
        sp=([0x2b9b0,0x2b9bc,0x2c1ec,HEAP+80,1][i%5] if overlap else [HEAP+3000+i%4,1,0xfffffffd][i%3])
        rr[0]=obj;rr[4]=sp
        vals=[0,1,0x7fffffff,0x80000000,0xffffffff,0xfffffffd,rng.getrandbits(32)]
        for k,off in enumerate([12,16,20,68]):put(obj+off,vals[(i+k)%len(vals)])
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5))
        expected=[]
        def store(a,v):expected.append((a&MASK,4,v&MASK));put(a,v)
        # Independent summary follows the real ordering, including post-store reloads.
        store(sp-4,CODE+0x2b760);store(0x2b9ac,obj);store(0x2b9b8,rr[3])
        oldx=read(obj+12);store(sp-8,3);oldy=read(obj+16)
        endx=(rr[1]+oldx)&MASK;endy=(rr[6]+oldy)&MASK
        height=read(obj+68);z=read(obj+20)
        signedheight=height if height<0x80000000 else height-(1<<32)
        store(0x2b9f8,0);shootz=((signedheight>>1)+z+0x80000)&MASK
        store(0x2b9a8,shootz);store(0x2c1e4,0xffff6000)
        newy=read(obj+16);newx=read(obj+12);store(0x2c1e8,0xa000)
        store(sp-12,CODE+0x2bbff)
        wanted=[newx,endy,newy,endx,(sp-12)&MASK,0xa000,endy,z]
        writes.clear();visits.clear()
        em.emu_start(CODE+0x2bba0,CODE+0x2c8a0,count=25)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2c8a0,'wrong call destination')
        require(len(visits)==25,'wrong instruction count')
        require([em.reg_read(r) for r in regs]==wanted,'wrong registers')
        require(writes==expected,'wrong write order')
        for a,b in pages.items():require(em.mem_read(a,4096)==b,'wrong mapped data memory')
      groups['overlapping' if overlap else 'separated']={'cases':512}
    return {'total_cases':1024,'groups':groups,'checks':'registers, all mapped data memory, store order, real CALL, signed odd heights, coordinate overflow, unaligned/wrapping stacks, aliased actor/global/stack reads',
      'code_pointers':'callback and CALL return address relocated to emulated code base; formal model uses code-relative offsets',
      'scope':'stops at P_PathTraverse entry; traversal/callback not executed; flags not compared'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cross-check',action='store_true');args=p.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-aim-setup.json').read_text());profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec,allowed_objects=(1,3))
    out=ROOT/'artifacts/original-aim-setup';out.mkdir(parents=True,exist_ok=True)
    source=out/'Extracted.lean';source.write_text(certificate(raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSetup'],cwd=ROOT,check=True)
    result=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(result.stdout);(out/'axioms.log').write_text(result.stdout)
    report={'exe_sha256':profile['exe_sha256'],'units':spec['units'],'axioms':result.stdout.splitlines(),
      'scope':'25-instruction setup and CALL, reusable 36-instruction query prefix, post-sound firing prefix <=163. Production geometry input correspondence requires shooter/range/table encoding and separation. Traversal and callback bodies, preserved return frame, initialization and loader remain open.',
      'cross_check':cross_check(raw) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original aim setup, traversal-call joins, kernel certificates and axiom audit.')
    if args.cross_check:print('Native setup cases:',report['cross_check']['total_cases'])
if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as e:print(e.stdout or '');print(e.stderr or '');raise

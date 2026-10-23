#!/usr/bin/env python3
"""Verify original P_LoadSideDefs publication and side-to-sector pointer writes."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
NAMES=['publish_checked','link_checked','pointer_checked']
NAMES+=['Doom.Proofs.OriginalSideLoader.'+n for n in ['decoded','publish_execution','link_execution','publish_patch','link_patch','untouched','target_value','pointer_value','graph_pointer','nonnegative_offset','link_execution_pointer']]
def certificate(raw):
    s='''import Doom.Proofs.OriginalSideLoader
namespace Doom.Verification.ExtractedSideLoader
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalSideLoader
'''
    for name,b in raw.items():
        s+=f'def {name} : List UInt8 := ['+','.join(hex(v) for v in b)+f']\ntheorem {name}_checked : {name}=OriginalSideLoader.{name}Bytes := by decide +kernel\n'
    s+='''theorem pointer_checked (s : X86Memory.State) (f : Option Flags) (index : BitVec 16) (base : Word)
    (source : load16 s.memory (s.regs 3+28)=index)
    (sectors : load32 s.memory 0x2c148=base) (safe : Apart 0x2c148 (s.regs 4))
    (valid : index.toNat<32768) :
    ∃ out, X86Routine.run (bytesProgram publish link) [0x2e4d1] 11 ⟨s,f,0x2e4af⟩=some out ∧
      out.core.memory=E1M1NoiseImage.applyPatch (linkPatch s) s.memory ∧
      load32 out.core.memory (s.regs 2+14)=base+BitVec.ofNat 32 (index.toNat*86) := by
  rw [publish_checked,link_checked]
  exact link_execution_pointer s f index base source sectors safe valid
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedSideLoader\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedSideLoader.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Independent instruction execution; complements, does not replace, Lean."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e4af);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for n,pc in [('publish',0x2e415),('link',0x2e4af)]:em.mem_write(CODE+pc,raw[n])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    page_addrs=[0,0x2c000,0x600000,0xfffff000]
    for a in page_addrs:em.mem_map(a,4096)
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    cases=0
    for mode in range(8):
        for index in list(range(85))+[32767,32768,65535,65534,256]:
            pages={a:bytearray(rng.randbytes(4096)) for a in page_addrs}
            def put(a,v,n=4):
                for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                    z=(a+k)&mask;pages[z&~4095][z&4095]=b
            def get(a,n=4):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
            rr=[rng.getrandbits(32) for _ in regs]
            rr[2]=0x600401+mode%4;rr[3]=0x600201+mode%4;rr[4]=0x600801+mode%4
            if mode==2:rr[4]=mask
            if mode==3:rr[4]=0x2c148
            if mode==4:rr[4]=0x2c147
            if mode==5:rr[2]=rr[4]-14
            if mode==6:rr[3]=rr[4]-28
            if mode==7:rr[3]=rr[2]+14-28
            put(0x2c148,rng.getrandbits(32));put(rr[3]+28,index,2)
            for a,b in pages.items():em.mem_write(a,bytes(b))
            for r,v in zip(regs,rr):em.reg_write(r,v)
            em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
            em.emu_start(CODE+0x2e4af,CODE+0x2e4d1,count=12)
            signed=index if index<32768 else index-65536
            off=(signed*86)&mask;stack=rr[4];dest=(rr[2]+14)&mask
            put(stack,off);value=(get(0x2c148)+off)&mask;put(dest,value)
            rr[0]=value;rr[1]=(rr[1]+30)&mask;rr[2]=(rr[2]+18)&mask
            rr[3]=(rr[3]+30)&mask;rr[5]=(rr[5]+1)&mask;rr[7]=(rr[7]+30)&mask
            require(writes==[(stack,4,off),(dest,4,value)],f'ordered writes/{mode}/{index}')
            require([em.reg_read(r) for r in regs]==rr,f'registers/{mode}/{index}')
            require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory/{mode}/{index}')
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2e4d1 and len(visits)==11,'endpoint/count')
            cases+=1
    for i in range(64):
        rr=[rng.getrandbits(32) for _ in regs];page=bytearray(rng.randbytes(4096));em.mem_write(0x2c000,bytes(page))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        flags=2|(rng.getrandbits(12)&0x8d5);em.reg_write(x.UC_X86_REG_EFLAGS,flags)
        writes.clear();visits.clear();em.emu_start(CODE+0x2e415,CODE+0x2e41c,count=3)
        page[0x118:0x11c]=rr[0].to_bytes(4,'little');rr[3]=rr[0]
        require(writes==[(0x2c118,4,rr[0])] and bytes(em.mem_read(0x2c000,4096))==page,'publication memory')
        require([em.reg_read(r) for r in regs]==rr and em.reg_read(x.UC_X86_REG_EFLAGS)==flags,'publication registers/flags')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2e41c and len(visits)==2,'publication endpoint/count')
    return dict(link_cases=cases,publish_cases=64,all_registers=True,ordered_writes=True,mapped_memory_frame=True,
        signed_indices=True,unaligned_and_wrapping_writes=True,aliased_scratch_global_source_destination=True,
        publication_flags=True,scope='Local segment executions with generated states, not startup reachability or a full loader run.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-side-loader.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-side-loader';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-image')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalSideLoader'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original side-table publication and sector-pointer emission refine sparse initialization.')
if __name__=='__main__':main()

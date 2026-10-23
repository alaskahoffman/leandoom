#!/usr/bin/env python3
"""Original P_LoadLineDefs cached pointers establish the grouping scan's inputs."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_original_noise_topology as topology
ROOT,require=extraction.ROOT,extraction.require
NAMES=['cache_checked','inputs_checked']
NAMES+=['Doom.Proofs.OriginalLineCache.'+n for n in ['decoded','front_execution','back_execution','joined_execution','cached_memory','cached_reg','fields_apart','readback','frame','sentinel','lookup']]
NAMES+=['Doom.Proofs.E1M1LineCache.'+n for n in ['source_values','establishes','extend_inputs','physical_line']]
def certificate(raw):
    s='''import Doom.Proofs.E1M1LineCache
namespace Doom.Verification.ExtractedLineCache
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalLineCache E1M1LineCache
'''
    s+='def cache : List UInt8 := ['+','.join(hex(v) for v in raw['cache'])+']\n'
    s+='''theorem cache_checked : cache=cacheBytes := by decide +kernel
theorem inputs_checked (e : OriginalGroupOutput.Line) (old : List OriginalGroupOutput.Line)
    (s : X86Memory.State) (f : Option Flags) (h : Source e s)
    (before : OriginalGroupOutput.Inputs old s.memory)
    (safe : ∀ l∈old, ∀ off∈[(46#32),50],
      Apart (l.address+off) (e.address+46) ∧ Apart (l.address+off) (e.address+50)) :
    ∃ out, X86Routine.run (bytesProgram cache) [0x2e3ac] 16 ⟨s,f,0x2e368⟩=some out ∧
      OriginalGroupOutput.Inputs (e::old) out.core.memory := by
  rw [cache_checked]
  exact extend_inputs e old s f h before safe
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedLineCache\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedLineCache.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,data):
    """Original instructions vs independent ordered byte-memory model. Synthetic
    layouts include every pinned E1M1 line and malformed signed indices/aliases."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e368);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    em.mem_write(CODE+0x2e368,raw['cache'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    # Sparse pages selected per case keep full-memory comparisons inexpensive.
    mapped=set();writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    def signed16(i):return i if i<32768 else i-65536
    cases=[(e[2],e[3],i%4,0,e[4],e[5]) for i,e in enumerate(data['lines'])]
    edges=[0,1,647,32767,32768,65534,65535]
    cases += [(f,b,a,0,3,7) for f in edges for b in edges for a in range(4)]
    cases += [(0,1,a,m,3,7) for a in range(4) for m in [1,2,3]]
    for case,(fi,bi,align,mode,fs,bs) in enumerate(cases):
        for a in mapped:em.mem_unmap(a,4096)
        mapped.clear();pages={}
        def ensure(a):
            p=(a&mask)&~4095
            if p not in pages:pages[p]=bytearray(rng.randbytes(4096))
        def put(a,v,n=4):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;ensure(z);pages[z&~4095][z&4095]=b
        def get(a,n=4):
            for k in range(n):ensure(a+k)
            return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        line=0x680101+align;base=0x600001+align
        if mode==1:line=0x2c118-46 # front write replaces side-base global
        if mode==2:base=line+46-18-14 # back lookup reads the just-written front pointer
        if mode==3:base=line+47-18-14 # partially overlapping back lookup
        fv=0x610001+86*fs;bv=0x610001+86*bs
        if mode==1:fv=0x620001
        put(0x2c118,base);put(line+22,fi,2);put(line+24,bi,2)
        if fi!=65535:put(base+signed16(fi)*18+14,fv)
        if bi!=65535:put(base+signed16(bi)*18+14,bv)
        if mode==1:put(fv+signed16(bi)*18+14,bv)
        for a in [line+46,line+49,line+50,line+53]:ensure(a)
        for a,b in pages.items():em.mem_map(a,4096);mapped.add(a);em.mem_write(a,bytes(b))
        rr=[rng.getrandbits(32) for _ in regs];rr[3]=line
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        em.emu_start(CODE+0x2e368,CODE+0x2e3ac,count=17)
        expected=[];expected_steps=0;final_absent=False
        for off,dest in [(22,46),(24,50)]:
            i=get(line+off,2);rr[0]=signed16(i)&mask;final_absent=i==65535
            if final_absent:v=0;expected_steps+=4
            else:
                rr[2]=get(0x2c118);rr[0]=get(rr[2]+signed16(i)*18+14);v=rr[0];expected_steps+=8
            expected.append((line+dest,4,v));put(line+dest,v)
        require(writes==expected,f'ordered writes/{case}')
        if case<len(data['lines']):
            require([v for _,_,v in writes]==[0x610001+86*fs,0 if bi==65535 else 0x610001+86*bs],f'WAD sector pointers/{case}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{case}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),f'memory/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2e3ac and len(visits)==expected_steps,f'endpoint/count/{case}')
        if final_absent:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,f'known flags/{case}')
    return dict(cases=len(cases),wad_lines=len(data['lines']),edge_cases=len(cases)-len(data['lines']),all_registers=True,
        ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,signed_indices=True,unaligned=True,
        aliased_side_global_and_back_lookup=True,scope='Local segments at synthetic layouts; not complete DOS initialization.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-line-cache.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    data,wad_profile=topology.pinned_data();require(profile['exe_sha256']==wad_profile['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-line-cache';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineCache'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wad_profile['wad_sha256'],
        audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original cached-sector stores establish and preserve grouping inputs.')
if __name__=='__main__':main()

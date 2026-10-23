#!/usr/bin/env python3
"""Original WAD side-index copies, sector caches and loader-loop advance."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_original_noise_topology as topology
ROOT,require=extraction.ROOT,extraction.require
NAMES=['copy_checked','cache_checked','advance_checked','inputs_checked']
NAMES+=['Doom.Proofs.HalfMemory.'+n for n in ['translate','half_frame','word_frame','readback']]
NAMES+=['Doom.Proofs.OriginalLineLoad.'+n for n in ['decoded','ax_low','copy_execution','advance_execution','cache_agrees','local_agrees','joined_execution','copied_indices','copied_frame','progress']]
NAMES+=['Doom.Proofs.E1M1LineLoad.'+n for n in ['target_preserved','cache_source','establishes','frame']]
def certificate(raw):
    s="""import Doom.Proofs.E1M1LineLoad
namespace Doom.Verification.ExtractedLineLoad
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalLineLoad E1M1LineLoad
"""
    for name in ['copy','cache','advance']:
        owner='OriginalLineCache' if name=='cache' else 'OriginalLineLoad'
        s+=f'def {name} : List UInt8 := ['+','.join(hex(v) for v in raw[name])+f']\ntheorem {name}_checked : {name}={owner}.{name}Bytes := by decide +kernel\n'
    s+="""theorem inputs_checked (e : OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (h : Source e s) :
    ∃ out, X86Routine.run (joinedBytes copy cache advance) [0x2e29a,0x2e3c1] 26 ⟨s,f,0x2e358⟩=some out ∧
      OriginalGroupOutput.Inputs [e] out.core.memory ∧
      out.core.regs 1=s.regs 1+14 ∧ out.core.regs 3=e.address+62 ∧ out.core.regs 5=s.regs 5+1 := by
  rw [copy_checked,cache_checked,advance_checked]
  exact establishes e s f h
"""
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedLineLoad\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedLineLoad.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,data):
    """Independent original-instruction diagnostic, with byte-ordered memory.
    Generated layouts are not a claim about the DOS allocator or full startup."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e358);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for name,pc in [('copy',0x2e358),('cache',0x2e368),('advance',0x2e3ac)]:em.mem_write(CODE+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    mapped=set();writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    def visit(e,a,_n,_d):
        if a-CODE in [0x2e29a,0x2e3c1]:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    def signed16(i):return i if i<32768 else i-65536
    def signed32(i):return i if i<0x80000000 else i-0x100000000
    cases=[(e[2],e[3],i%4,0,i,475,e[4],e[5]) for i,e in enumerate(data['lines'])]
    edge=[0,1,647,32767,32768,65534,65535]
    cases += [(f,b,a,0,0,1,3,7) for f in edge for b in edge for a in range(4)]
    cases += [(0,1,a,m,4,9,3,7) for a in range(4) for m in range(1,7)]
    cases += [(0,1,0,0,i,n,3,7) for i in [0,474,475,0x7ffffffe,0x7fffffff,0xfffffffe,0xffffffff] for n in [0,1,475,0x7fffffff,0x80000000,0xffffffff]]
    loop=done=0
    for case,(fi,bi,align,mode,counter,count,fs,bs) in enumerate(cases):
        for a in mapped:em.mem_unmap(a,4096)
        mapped.clear();initial={};memory={};model_writes=[]
        def ensure(a):
            p=(a&mask)&~4095
            if p not in initial:
                initial[p]=bytearray(rng.randbytes(4096));memory[p]=initial[p].copy()
        def put(a,v,n=4,seed=False):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;ensure(z);memory[z&~4095][z&4095]=b
                if seed:initial[z&~4095][z&4095]=b
        def get(a,n=4):
            for k in range(n):ensure(a+k)
            return int.from_bytes(bytes(memory[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        def store(a,v,n=4):model_writes.append((a&mask,n,v&((1<<(8*n))-1)));put(a,v,n)
        line=0x680101+align;record=0x690101+align;base=0x600001+align
        if mode==1:record=line+10 # first destination overwrites second source
        if mode==2:record=line+11 # partial source/destination overlap
        if mode==3:line=0x2c118-46 # front cache overwrites side-base global
        if mode==4:base=line+46-18-14 # back side lookup observes front cache
        if mode==5:line=0x2c134-46 # front cache overwrites the count read by advance
        if mode==6:record=0xfffffff5 # raw WAD word crosses address wrap
        put(0x2c118,base,seed=True);put(0x2c134,count,seed=True)
        put(record+10,fi,2,True);put(record+12,bi,2,True)
        if fi!=65535:put(base+signed16(fi)*18+14,0x610001+86*fs,seed=True)
        if bi!=65535:put(base+signed16(bi)*18+14,0x610001+86*bs,seed=True)
        rr=[rng.getrandbits(32) for _ in regs];rr[1]=record;rr[3]=line;rr[5]=counter;before=rr.copy()
        flags=2|(rng.getrandbits(12)&0x8d5)
        # An independent instruction-level model retains AX's high bits.
        first=get(record+10,2);rr[0]=(rr[0]&0xffff0000)|first;store(line+22,first,2)
        second=get(record+12,2);rr[0]=(rr[0]&0xffff0000)|second;store(line+24,second,2)
        copy_eax=rr[0];expected_steps=10
        for off,dest in [(22,46),(24,50)]:
            i=get(line+off,2);rr[0]=signed16(i)&mask
            if i==65535:v=0;expected_steps+=4
            else:
                rr[2]=get(0x2c118);rr[0]=get(rr[2]+signed16(i)*18+14);v=rr[0];expected_steps+=8
            store(line+dest,v)
        rr[6]=get(0x2c134);rr[5]=(rr[5]+1)&mask;rr[1]=(rr[1]+14)&mask;rr[3]=(rr[3]+62)&mask
        endpoint=0x2e29a if signed32(rr[5])<signed32(rr[6]) else 0x2e3c1
        delta=(rr[5]-rr[6])&mask;sign=(delta>>31)&1;overflow=((rr[5]^rr[6])&(rr[5]^delta))>>31
        expected_flags=(0x40 if delta==0 else 0)|(0x80 if sign else 0)|(0x800 if overflow else 0)
        for a,b in initial.items():em.mem_map(a,4096);mapped.add(a);em.mem_write(a,bytes(b))
        for r,v in zip(regs,before):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear()
        # Check the copy-only boundary too, including preserved flags/high EAX.
        em.emu_start(CODE+0x2e358,CODE+0x2e368,count=5)
        require(em.reg_read(x.UC_X86_REG_EAX)==copy_eax and em.reg_read(x.UC_X86_REG_EFLAGS)==flags,f'AX/flags/{case}')
        em.emu_start(CODE+0x2e368,CODE+0x2e3c1,count=23)
        require(writes==model_writes,f'ordered writes/{case}')
        require([em.reg_read(r) for r in regs]==rr,f'registers/{case}')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in memory.items()),f'full memory/{case}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c0==expected_flags,f'final modeled flags/{case}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+endpoint and len(visits)==expected_steps,f'endpoint/count/{case}')
        if case<len(data['lines']):
            require([v for _,_,v in writes]==[fi,bi,0x610001+86*fs,0 if bi==65535 else 0x610001+86*bs],f'WAD values/{case}')
        loop+=endpoint==0x2e29a;done+=endpoint==0x2e3c1
    return dict(cases=len(cases),wad_lines=len(data['lines']),edge_cases=len(cases)-len(data['lines']),loop_edges=loop,cleanup_edges=done,
        all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,copy_flags_and_upper_eax=True,
        signed_indices_and_counts=True,aliasing_and_wrapping=True,
        scope='Local suffix runs on synthetic layouts; no earlier geometry, whole loader loop or startup reachability.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for name in ['original-line-load','original-line-cache']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wad_profile=topology.pinned_data();require(profile['exe_sha256']==wad_profile['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-line-load';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineLoad'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wad_profile['wad_sha256'],
        audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
        scope='WAD side-index copies through cached sectors and loop advance, with explicit memory contracts. Geometry and full loader startup remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original side-index copies, cached pointers and loop advance establish grouping inputs.')
if __name__=='__main__':main()

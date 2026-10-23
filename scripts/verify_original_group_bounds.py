#!/usr/bin/env python3
"""Verify the original two bounding-box calls and the P_GroupLines scan advance."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
UNITS={'box':0x241e0,'first':0x2e682,'second':0x2e690,'advance':0x2e6a2}
NAMES=[n+'_checked' for n in UNITS]+['joined_checked']
NAMES+=['Doom.Proofs.OriginalGroupBounds.'+n for n in ['decoded','horizontal_execution','vertical_execution','first_execution','second_execution','advance_execution','box_path','horizontal_frame','vertical_frame','stack_apart','call_return','first_return','second_return','joined_execution']]
def certificate(raw):
    s='''import Doom.Proofs.OriginalGroupBounds
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Doom.Verification.ExtractedGroupBounds
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalGroupBounds
'''
    for n in UNITS:
        s+='def '+n+' : List UInt8 := ['+','.join(hex(v) for v in raw[n])+']\n'
        s+='theorem '+n+'_checked : '+n+'='+n+'Bytes := by decide +kernel\n'
    s+='''theorem joined_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram box first second advance) exits 38 ⟨s,f,0x2e682⟩=some (result s) := by
  rw [box_checked,first_checked,second_checked,advance_checked]; exact joined_execution s f
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedGroupBounds\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedGroupBounds.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Execute original bytes independently, comparing the complete mapped state.

    The emulator code segment is based at CODE; return words therefore contain
    CODE+offset. Data operands retain the formal model's original data offsets.
    """
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x241e0);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for n,pc in UNITS.items():em.mem_write(CODE+pc,raw[n])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    page_addrs=[0,0x2c000,0x600000,0xfffff000]
    for a in page_addrs:em.mem_map(a,4096)
    writes=[];visits=[];stops=set()
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE in stops:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    def signed(v):return v if v<0x80000000 else v-0x100000000
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    coverage=dict(x_min=0,x_max=0,x_keep=0,y_min=0,y_max=0,y_keep=0,loop=0,done=0)
    total=0
    for joined in [False,True]:
      for mode in range(6):
       for case in range(32):
        pages={a:bytearray(rng.randbytes(4096)) for a in page_addrs}
        def put(a,v,n=4):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a,n=4):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        rr=[rng.getrandbits(32) for _ in regs]
        sp=[0x600800,0xfffffff4,0x600801,0x600800,0x2c134,0x600800][mode]
        rr[4]=sp;rr[0]=sp;rr[1]=0x600100;rr[7]=[0,474,475,0x7fffffff,0xfffffffe,0xffffffff][case%6]
        rr[6]=[0x600b00,0xffffffff][case%2]
        points=[0,1,0xffffffff,0x80000000,0x7fffffff,10,0xfffffff6,rng.getrandbits(32)]
        rr[2]=points[case%8];rr[3]=points[(case//4)%8]
        # Include normal, empty/inverted, equal and signed-extreme bounds.
        bounds=[(10,0xfffffff6,0xfffffff6,10),(0x80000000,0x7fffffff,0x7fffffff,0x80000000),(0,0,0,0),(0x7fffffff,0x80000000,0x80000000,0x7fffffff)][case%4]
        for i,v in enumerate(bounds):put(sp+4*i,v)
        if joined:
            put(rr[1],0x600400);put(rr[1]+4,sp if mode==3 else 0x600600)
            put(0x600400,rr[2]);put(0x600404,rr[3]);put(0x600600,points[(case+2)%8]);put(0x600604,points[(case+3)%8])
            put(0x2c134,[0,1,475,0x80000000,0x7fffffff,0xffffffff][case%6])
            if mode==5:
                # The first Y minimum write replaces the second vertex pointer.
                rr[1]=sp;put(sp,0x600400);put(sp+4,0x600700)
                put(0x600404,0x600600)
            start=0x2e682;stops={0x2e676,0x2e6af}
        else:
            # A standalone helper also permits a box overlapping the return word.
            rr[4]=sp+8 if mode==5 else 0x600a00
            put(rr[4],CODE+0x2e6af);start=0x241e0;stops={0x2e6af}
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v&mask)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        expected=[];steps=0;flags=0
        def store(a,v):put(a,v);expected.append((a&mask,4,v&mask))
        def box():
            nonlocal steps,flags
            base=rr[0];lo=get(base+8);flags=cmpflags(rr[2],lo);steps+=2
            if signed(rr[2])<signed(lo):store(base+8,rr[2]);steps+=2;coverage['x_min']+=1
            else:
                hi=get(base+12);flags=cmpflags(rr[2],hi);steps+=2
                if signed(rr[2])>signed(hi):store(base+12,rr[2]);steps+=1;coverage['x_max']+=1
                else:coverage['x_keep']+=1
            lo=get(base+4);flags=cmpflags(rr[3],lo);steps+=2
            if signed(rr[3])<signed(lo):store(base+4,rr[3]);steps+=1;coverage['y_min']+=1
            else:
                hi=get(base);flags=cmpflags(rr[3],hi);steps+=2
                if signed(rr[3])>signed(hi):store(base,rr[3]);steps+=1;coverage['y_max']+=1
                else:coverage['y_keep']+=1
            pc=get(rr[4]);rr[4]=(rr[4]+4)&mask;steps+=1
            return pc
        if joined:
            rr[2]=get(rr[1]);rr[0]=rr[4];rr[3]=get(rr[2]+4);rr[2]=get(rr[2]);steps+=5
            rr[4]=(rr[4]-4)&mask;store(rr[4],CODE+0x2e690)
            require(box()==CODE+0x2e690,'first return')
            rr[0]=get(rr[1]+4);rr[3]=get(rr[0]+4);rr[2]=get(rr[0]);rr[0]=rr[4];rr[6]=(rr[6]+4)&mask;steps+=6
            rr[4]=(rr[4]-4)&mask;store(rr[4],CODE+0x2e6a2)
            require(box()==CODE+0x2e6a2,'second return')
            rr[0]=get(0x2c134);rr[7]=(rr[7]+1)&mask;rr[1]=(rr[1]+62)&mask;flags=cmpflags(rr[7],rr[0]);steps+=5
            loop=signed(rr[7])<signed(rr[0]);pc=CODE+(0x2e676 if loop else 0x2e6af);coverage['loop' if loop else 'done']+=1
        else:
            pc=box()
            # RET can be overwritten by the box in standalone malformed layouts.
            stops={pc-CODE}
        em.emu_start(CODE+start,pc,count=40)
        label=f'{joined}/{mode}/{case}'
        require(writes==expected,'ordered writes '+label)
        require([em.reg_read(r) for r in regs]==rr,'registers '+label)
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),'memory frame '+label)
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'flags '+label)
        require(em.reg_read(x.UC_X86_REG_EIP)==pc and len(visits)==steps,'endpoint/count '+label)
        total+=1
    require(all(coverage.values()),'branch coverage')
    return dict(cases=total,branches=coverage,all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,
        wrapping_unaligned_box=True,aliased_vertex_and_global_reads=True,scope='Original helper and joined two calls plus scan advance; not a complete scan.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-group-bounds.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-group-bounds';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupBounds'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original bounding-box helper, both calls/returns and scan advance.')
if __name__=='__main__':main()

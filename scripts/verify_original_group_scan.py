#!/usr/bin/env python3
"""Certify original line selection, complete per-sector scan and finite bound."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_original_noise_topology as topology
ROOT,require=extraction.ROOT,extraction.require
UNITS={'group':0x2e661,'box':0x241e0,'first':0x2e682,'second':0x2e690,'advance':0x2e6a2}
NAMES=[n+'_checked' for n in UNITS]+['program_checked','scan_checked','layout_checked']
NAMES+=['Doom.Proofs.OriginalGroupStep.'+n for n in ['selection_agrees','bounds_agrees','iteration_path','iteration_registers','iteration_count','iteration_exit','iteration_progress']]
NAMES+=['Doom.Proofs.OriginalGroupScan.'+n for n in ['ready_safe','ready_step','scan_path','scan_execution','e1m1_scan','entry_ready','entry_execution']]
def certificate(raw):
    s='''import Doom.Proofs.OriginalGroupScan
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace Doom.Verification.ExtractedGroupScan
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalGroupStep OriginalGroupScan
'''
    for n in UNITS:
        parent='OriginalGroupLines' if n=='group' else 'OriginalGroupBounds'
        s+='def '+n+' : List UInt8 := ['+','.join(hex(v) for v in raw[n])+']\n'
        s+='theorem '+n+'_checked : '+n+'='+parent+'.'+n+'Bytes := by decide +kernel\n'
    s+='''def extracted : X86Routine.Program := fun pc =>
  if 0x2e661≤pc ∧ pc<0x2e682 then OriginalGroupLines.bytesProgram group pc
  else OriginalGroupBounds.bytesProgram box first second advance pc
theorem program_checked : extracted=program := by
  rfl
theorem scan_checked (s : X86Memory.State) (f : Option Flags)
    (layout : Layout 475 (s.regs 4) (s.regs 6))
    (count : (load32 s.memory 0x2c134).toNat=475)
    (safe : Apart 0x2c134 (s.regs 5+82)) :
    ∃ out, X86Routine.run extracted [0x2e6af] 20431 ⟨s,f,0x2e661⟩=some out ∧
      out.pc=0x2e6af ∧ Ready 475 (s.regs 4) (s.regs 6) 475 out.core := by
  rw [program_checked]; exact OriginalGroupScan.entry_execution 475 s f layout count safe
-- A concrete finite layout witnesses that the storage conditions are satisfiable.
-- These addresses are a witness, not a claim about DOS startup allocation.
private theorem stack_checked : StackSafe 0x600800 := by
  constructor <;> unfold Apart <;> decide +kernel
private theorem output_checked : ∀ j : Fin 475, Apart 0x2c134 (cursor 0x610000 j.val) := by
  unfold Apart
  decide +kernel
theorem layout_checked : Layout 475 0x600800 0x610000 :=
  ⟨by decide,stack_checked,fun j hj => output_checked ⟨j,hj⟩⟩
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedGroupScan\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedGroupScan.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Independent complete executions of the original entry and scanning loop."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e676);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for n,pc in UNITS.items():em.mem_write(CODE+pc,raw[n])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    page_addrs=[0,0x2c000,0xfffff000]+list(range(0x600000,0x620000,4096))
    for a in page_addrs:em.mem_map(a,4096)
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE==0x2e6af:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    def signed(v):return v if v<0x80000000 else v-0x100000000
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    coverage=dict(empty=0,front=0,back=0,skip=0,self_edge=0,iterations=0)
    cases=0;largest=0
    for total in [0,1,2,7,475]:
      for mode in range(6):
       for align in [0,1]:
        pages={a:bytearray(rng.randbytes(4096)) for a in page_addrs}
        def put(a,v,n=4):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;pages[z&~4095][z&4095]=b
        def get(a,n=4):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        rr=[rng.getrandbits(32) for _ in regs];sp=0xfffffff4 if mode==4 else 0x600800+align
        rr[4]=sp;rr[5]=0x600900+align;rr[6]=0x618000+align
        linebase=0x601000+align
        if mode==5:rr[6]=linebase # Output overwrites the first line's vertex pointer.
        for i,v in enumerate([0x80000000,0x7fffffff,0x7fffffff,0x80000000]):put(sp+4*i,v)
        put(0x2c120,linebase);put(0x2c134,total)
        for i in range(total):
            line=linebase+62*i;vertex=0x610000+16*i+align
            put(line,vertex);put(line+4,vertex+8)
            branch=(i%4) if mode in [2,4,5] else [0,1,0,3][mode]
            put(line+46,rr[5] if branch in [0,2] else 0)
            put(line+50,rr[5] if branch in [1,2] else 0)
            for k in range(4):put(vertex+4*k,rng.getrandbits(32))
        for a,b in pages.items():em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        expected=[];steps=0;flags=0
        def store(a,v):put(a,v);expected.append((a&mask,4,v&mask))
        def box():
            nonlocal steps,flags
            base=rr[0];lo=get(base+8);flags=cmpflags(rr[2],lo);steps+=2
            if signed(rr[2])<signed(lo):store(base+8,rr[2]);steps+=2
            else:
                hi=get(base+12);flags=cmpflags(rr[2],hi);steps+=2
                if signed(rr[2])>signed(hi):store(base+12,rr[2]);steps+=1
            lo=get(base+4);flags=cmpflags(rr[3],lo);steps+=2
            if signed(rr[3])<signed(lo):store(base+4,rr[3]);steps+=1
            else:
                hi=get(base);flags=cmpflags(rr[3],hi);steps+=2
                if signed(rr[3])>signed(hi):store(base,rr[3]);steps+=1
            pc=get(rr[4]);rr[4]=(rr[4]+4)&mask;steps+=1
            return pc
        rr[7]=0;rr[1]=get(0x2c120);rr[3]=get(0x2c134);store(rr[5]+82,rr[6]);steps+=6
        flags=(int(rr[3]==0)<<6)|((rr[3]>>31)<<7)
        if total==0:coverage['empty']+=1
        while rr[7]<total:
            coverage['iterations']+=1
            front=get(rr[1]+46);back=get(rr[1]+50);flags=cmpflags(rr[5],front);steps+=2
            if rr[5]==front:
                selected=True;coverage['front']+=1
                if rr[5]==back:coverage['self_edge']+=1
            else:
                flags=cmpflags(rr[5],back);steps+=2;selected=rr[5]==back
                coverage['back' if selected else 'skip']+=1
            if selected:
                store(rr[6],rr[1]);steps+=1
                rr[2]=get(rr[1]);rr[0]=rr[4];rr[3]=get(rr[2]+4);rr[2]=get(rr[2]);steps+=5
                rr[4]=(rr[4]-4)&mask;store(rr[4],CODE+0x2e690);require(box()==CODE+0x2e690,'first return')
                rr[0]=get(rr[1]+4);rr[3]=get(rr[0]+4);rr[2]=get(rr[0]);rr[0]=rr[4];rr[6]=(rr[6]+4)&mask;steps+=6
                rr[4]=(rr[4]-4)&mask;store(rr[4],CODE+0x2e6a2);require(box()==CODE+0x2e6a2,'second return')
            rr[0]=get(0x2c134);rr[7]=(rr[7]+1)&mask;rr[1]=(rr[1]+62)&mask;flags=cmpflags(rr[7],rr[0]);steps+=5
            require(rr[0]==total,'count frame')
        em.emu_start(CODE+0x2e661,CODE+0x2e6af,count=6+43*total+1)
        label=f'{total}/{mode}/{align}'
        require(writes==expected,'ordered writes '+label)
        require([em.reg_read(r) for r in regs]==rr,'registers '+label)
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),'memory frame '+label)
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'flags '+label)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2e6af and len(visits)==steps,'endpoint/count '+label)
        require(steps<=6+43*total,'proved bound '+label)
        cases+=1;largest=max(largest,steps)
    require(all(coverage.values()),'branch coverage')
    return dict(cases=cases,branches=coverage,largest_instruction_count=largest,all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,
        scope='Complete generated per-sector scans, including 475-line runs; not real DOS startup or WAD-list correspondence.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw={}
    for name in ['original-group-lines','original-group-bounds']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wad_profile=topology.pinned_data();require(len(data['lines'])==475,'pinned E1M1 line count');require(profile['exe_sha256']==wad_profile['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-group-scan';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupScan'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wad_profile['wad_sha256'],audited_declarations=len(NAMES),
        lines=475,scan_instruction_bound=20425,entry_instruction_bound=20431,axioms=r.stdout.splitlines(),cross_check=native,
        scope='Original per-sector scan terminates under explicit finite layout and count relations; output-list contents, full loader and runtime correspondence remain separate.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original scan entry, all iterations and termination under explicit finite layout conditions.')
if __name__=='__main__':main()

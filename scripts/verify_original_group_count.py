#!/usr/bin/env python3
"""Certify the original sector-line counting pass and allocation arguments."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_original_line_geometry as geometry
ROOT,require=extraction.ROOT,extraction.require
NAMES=['bytes_checked','entry_checked','body_checked','allocation_checked']
NAMES+=['Doom.Proofs.OriginalGroupCount.'+n for n in [
    'decoded','entry_execution','body_execution','branch_execution','iteration_path',
    'allocation_execution','frame','progress','stable_pointers','distinct_rule',
    'front_count','back_count','sector_count','inputs_preserved']]
def certificate(raw):
    s='''import Doom.Proofs.OriginalGroupCount
namespace Doom.Verification.ExtractedGroupCount
open X86 X86Memory X86Control Doom.Proofs.OriginalGroupCount
'''
    s+='def count : List UInt8 := ['+','.join(hex(v) for v in raw['count'])+']\n'
    s+='''theorem bytes_checked : count=countBytes := by decide +kernel
theorem entry_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram count) [0x2e602,0x2e62b] 6 ⟨s,f,0x2e5ef⟩=some (entry s) := by
  rw [bytes_checked]; exact entry_execution s f
theorem body_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram count) [0x2e629] 16 ⟨s,f,0x2e602⟩=some {result s with pc:=0x2e629} := by
  rw [bytes_checked]; exact body_execution s f
theorem allocation_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram count) [0x2e639] 3 ⟨s,f,0x2e62b⟩=some (allocation s) := by
  rw [bytes_checked]; exact allocation_execution s f
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedGroupCount\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedGroupCount.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,data):
    """Actual instructions against an independent ordered byte-memory model.
    Includes all E1M1 records, aliasing, unaligned/wrapping counters, and full passes.
    This is a runtime cross-check; it is not the universal Lean theorem."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    mask=0xffffffff;CODE=0x100000;rng=random.Random(0x2e602)
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    em.mem_write(CODE+0x2e5ef,raw['count'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    mapped=set();writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    def signed(v):return v if v<2**31 else v-2**32
    def run(initial,rr,start,stop,steps,expected,model,expected_pc):
        for a in mapped:em.mem_unmap(a,4096)
        mapped.clear()
        for a,b in initial.items():em.mem_map(a,4096);mapped.add(a);em.mem_write(a,bytes(b))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        em.emu_start(CODE+start,CODE+stop,count=steps)
        require(writes==expected,'ordered writes')
        require([em.reg_read(r) for r in regs]==model,'registers')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+expected_pc,'endpoint')
        require(len(visits)==steps,'instruction count')
    def memory():
        pages={}
        def ensure(a):
            p=(a&mask)&~4095
            if p not in pages:pages[p]=bytearray(rng.randbytes(4096))
        def put(a,v):
            for k,b in enumerate((v&mask).to_bytes(4,'little')):
                z=(a+k)&mask;ensure(z);pages[z&~4095][z&4095]=b
        def get(a):
            for k in range(4):ensure(a+k)
            return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(4)),'little')
        return pages,put,get
    # Body cases stop after the branch using an exact instruction budget.
    cases=[('wad',i,fs,0 if bi==65535 else bs+1) for i,(_ix,_fl,_fi,bi,fs,bs) in enumerate(data['lines'])]
    cases += [(kind,i,3,8) for kind in ['null','same','distinct','back-alias','front-alias','global-alias','wrap'] for i in range(8)]
    for kind,i,fs,bs in cases:
        pages,put,get=memory();line=0x680100+i%4;front=0x610001+86*fs;back=0 if bs==0 else 0x610001+86*(bs-1)
        if kind=='null':back=0
        if kind=='same':back=front
        if kind=='wrap':front=(0xfffffffe-78)&mask
        if kind=='back-alias':front=line+50-78;back=0x610200
        if kind=='front-alias':front=line+46-78;back=front
        if kind=='global-alias':front=0x2c134-78
        put(0x2c134,[475,0x7fffffff,0x80000000,0xffffffff][i%4]);put(line+46,front);put(line+50,back)
        if kind not in ['back-alias','front-alias','global-alias']:
            put(front+78,[0,1,0x7fffffff,0xffffffff][i%4])
        if back: get(back+78)
        # Prepare every page potentially touched after an aliasing count write.
        saved={a:bytearray(b) for a,b in pages.items()}
        f=get(line+46);put(f+78,get(f+78)+1);b=get(line+50);same=get(line+46)
        if b and b!=same:get(b+78)
        for a in pages:
            if a not in saved:saved[a]=bytearray(pages[a])
        pages.clear();pages.update({a:bytearray(b) for a,b in saved.items()})
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=line;rr[6]=[i,474,0x7fffffff,0xffffffff][i%4]
        model=rr.copy();expected=[]
        def store(a,v):expected.append((a&mask,4,v&mask));put(a,v)
        model[3]=get(model[0]+46);store(model[3]+78,get(model[3]+78)+1)
        model[7]=get(model[0]+50);model[2]=(model[2]+1)&mask
        second=bool(model[7] and model[7]!=get(model[0]+46))
        steps=11 if not model[7] else 13
        if second:
            model[1]=(get(model[7]+78)+1)&mask;model[2]=(model[2]+1)&mask;store(model[7]+78,model[1]);steps=17
        model[5]=get(0x2c134);model[6]=(model[6]+1)&mask;model[0]=(model[0]+62)&mask
        pc=0x2e602 if signed(model[6])<signed(model[5]) else 0x2e62b
        run(saved,rr,0x2e602,0x2e639,steps,expected,model,pc)
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),'body memory frame')
        diff=(model[6]-model[5])&mask
        flags=(0x40 if diff==0 else 0)|(0x80 if diff>>31 else 0)|(0x800 if ((model[6]^model[5])&(model[6]^diff))>>31 else 0)|(1 if model[6]<model[5] else 0)
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'body comparison flags')
    full=[]
    for align in range(4):
        pages,put,get=memory();line=0x680100+align;sector=0x610100+align
        put(0x2c120,line);put(0x2c134,len(data['lines']))
        for j in range(85):put(sector+86*j+78,0)
        for i,(_ix,_fl,_fi,bi,fs,bs) in enumerate(data['lines']):put(line+62*i+46,sector+86*fs);put(line+62*i+50,0 if bi==65535 else sector+86*bs)
        saved={a:bytearray(b) for a,b in pages.items()};rr=[rng.getrandbits(32) for _ in regs];model=rr.copy();expected=[]
        model[0]=line;model[7]=len(data['lines']);model[2]=model[6]=0;steps=6
        for _ in data['lines']:
            model[3]=get(model[0]+46);v=(get(model[3]+78)+1)&mask;expected.append((model[3]+78,4,v));put(model[3]+78,v)
            model[7]=get(model[0]+50);model[2]+=1;steps+=11 if not model[7] else 13
            if model[7] and model[7]!=get(model[0]+46):
                model[1]=(get(model[7]+78)+1)&mask;model[2]+=1;expected.append((model[7]+78,4,model[1]));put(model[7]+78,model[1]);steps+=4
            model[5]=get(0x2c134);model[6]+=1;model[0]+=62
        total=model[2];model[0]=(total*4)&mask;model[3]=0;model[2]=50;steps+=3
        run(saved,rr,0x2e5ef,0x2e639,steps,expected,model,0x2e639)
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),'full-pass memory frame')
        # Independent topology count, without consulting the register model.
        counts=[sum(fs==j or (bi!=65535 and bs==j) for _ix,_fl,_fi,bi,fs,bs in data['lines']) for j in range(85)]
        require([get(sector+86*j+78) for j in range(85)]==counts,'E1M1 sector incidence counts')
        require(total==sum(counts),'allocation total')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,'allocation flags')
        full.append(dict(alignment=align,lines=len(data['lines']),sector_links=total,allocation_bytes=total*4,instructions=steps))
    # Entry's signed nonpositive-count gate skips every line and requests zero bytes.
    for count in [0,0x80000000,0xffffffff]:
        pages,put,get=memory();put(0x2c120,0x680100);put(0x2c134,count)
        rr=[rng.getrandbits(32) for _ in regs];model=rr.copy();model[0]=model[3]=model[6]=0;model[2]=50;model[7]=count
        run(pages,rr,0x2e5ef,0x2e639,9,[],model,0x2e639)
        require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),'empty memory frame')
    return dict(body_cases=len(cases),full_passes=full,nonpositive_gates=3,all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,wrapping_and_aliasing=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,json.loads((ROOT/'tests/reference/original-group-count.json').read_text()))
    out=ROOT/'artifacts/original-group-count';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupCount'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=90)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    data,wp=geometry.geometry_data();native=cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wp['wad_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
      scope='Universal entry, ordered count iteration including backedge, frame/counter/input relations, and allocation arguments. Full 475-line runs are native cross-checks, not a whole-loop theorem. Startup reachability, initial counters, storage layout and allocator remain explicit obligations.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original sector-line counting instructions and allocation preparation.')
if __name__=='__main__':main()

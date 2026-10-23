#!/usr/bin/env python3
"""Pinned original vertex/delta prefix and bounds-through-loader suffix."""
import argparse,json,re,subprocess,struct
import verify_original_inline_thrust as extraction
import verify_original_noise_topology as topology
ROOT,require=extraction.ROOT,extraction.require
UNITS=['vertices','delta','horizontal','vertical','copy','cache','advance']
NAMES=[n+'_checked' for n in UNITS]+['prefix_checked','suffix_checked']
NAMES+=['Doom.Proofs.OriginalLineGeometry.'+n for n in ['decoded','vertices_execution','delta_execution','horizontal_execution','vertical_execution','prefix_execution','bounds_execution','vertices_readback','delta_readback','vertex_addresses','axis_frame','axis_minmax','bounds_frame','delta_frame','prepared_fields']]
NAMES+=['Doom.Proofs.E1M1LineGeometry.'+n for n in ['geometry_agrees','load_agrees','joined_execution','half_preserved','load_source','field_safe','bounds_survive','establishes']]
def certificate(raw):
    s="""import Doom.Proofs.E1M1LineGeometry
namespace Doom.Verification.ExtractedLineGeometry
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalLineGeometry E1M1LineGeometry
"""
    for name in UNITS:
        owner='OriginalLineCache' if name=='cache' else 'OriginalLineLoad' if name in ['copy','advance'] else 'OriginalLineGeometry'
        s+=f'def {name} : List UInt8 := ['+','.join(hex(v) for v in raw[name])+f']\ntheorem {name}_checked : {name}={owner}.{name}Bytes := by decide +kernel\n'
    s+="""theorem prefix_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram vertices delta horizontal vertical) [0x2e2ec] 18 ⟨s,f,0x2e2b2⟩=some (prepared s) := by
  rw [vertices_checked,delta_checked,horizontal_checked,vertical_checked]
  exact prefix_execution s f

theorem suffix_checked (e : OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (h : E1M1LineLoad.Source e s)
    (rawFront : SafeWord s (s.regs 1+10)) (rawBack : SafeWord s (s.regs 1+12))
    (base : SafeWord s 0x2c118)
    (frontSide : h.frontIndex≠65535 → SafeWord s (E1M1NoiseGraph.sideAddress h.sides h.frontIndex))
    (backSide : h.backIndex≠65535 → SafeWord s (E1M1NoiseGraph.sideAddress h.sides h.backIndex)) :
    ∃ out, X86Routine.run (joinedBytes vertices delta horizontal vertical copy cache advance)
      [0x2e29a,0x2e3c1] 42 ⟨s,f,0x2e326⟩=some out ∧
      OriginalGroupOutput.Inputs [e] out.core.memory ∧
      (∀ off∈[(34#32),38,30,26], load32 out.core.memory (e.address+off)=load32 (bounds s).core.memory (e.address+off)) := by
  rw [vertices_checked,delta_checked,horizontal_checked,vertical_checked,copy_checked,cache_checked,advance_checked]
  exact establishes e s f h rawFront rawBack base frontSide backSide
"""
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedLineGeometry\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedLineGeometry.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def geometry_data():
    data,profile=topology.pinned_data()
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/share['local_directory']/'doom1.wad').read_bytes()
    n,d=struct.unpack_from('<II',wad,4);lumps=[]
    for i in range(n):
        a,size,name=struct.unpack_from('<II8s',wad,d+16*i)
        lumps.append((name.rstrip(b'\0').decode('ascii'),wad[a:a+size]))
    start=next(i for i,(name,_) in enumerate(lumps) if name=='E1M1');source=dict(lumps[start+1:start+11])
    require(len(source['VERTEXES'])%4==0,'invalid vertex size')
    vertices=[((x<<16)&0xffffffff,(y<<16)&0xffffffff) for x,y in struct.iter_unpack('<hh',source['VERTEXES'])]
    records=list(struct.iter_unpack('<7H',source['LINEDEFS']))
    require(all(a<len(vertices) and b<len(vertices) for a,b,*_ in records),'bad vertex index')
    data['geometry']=[(a,b,*vertices[a],*vertices[b]) for a,b,*_ in records]
    return data,profile

def cross_check(raw,data):
    """Two separate original segments per input. The slope-classification gap is
    deliberately NOT executed or claimed equivalent by these diagnostics."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e326);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    starts=[0x2e2b2,0x2e2d6,0x2e326,0x2e33d,0x2e358,0x2e368,0x2e3ac]
    for name,pc in zip(UNITS,starts):em.mem_write(CODE+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    mapped=set();writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    def visit(e,a,_n,_d):
        if a-CODE in [0x2e2ec,0x2e29a,0x2e3c1]:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    def s16(i):return i if i<32768 else i-65536
    def s32(i):return i if i<0x80000000 else i-0x100000000
    cases=[(*g,i%4,0,i) for i,g in enumerate(data['geometry'])]
    edges=[0,1,2,32767,32768,65534,65535];coords=[0,1,0xffffffff,0x80000000,0x7fffffff,0xffff0000,0x10000]
    cases += [(a,b,*(rng.choice(coords) for _ in range(4)),align,0,-1) for a in edges for b in edges for align in range(4)]
    cases += [(0,1,*(rng.choice(coords) for _ in range(4)),align,mode,-1) for mode in range(1,9) for align in range(4)]
    for case,(i,j,x1,y1,x2,y2,align,mode,wad_id) in enumerate(cases):
        for a in mapped:em.mem_unmap(a,4096)
        mapped.clear();initial={};memory={};expected=[]
        def ensure(a):
            p=(a&mask)&~4095
            if p not in initial:initial[p]=bytearray(rng.randbytes(4096));memory[p]=initial[p].copy()
        def put(a,v,n=4,seed=False):
            for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                z=(a+k)&mask;ensure(z);memory[z&~4095][z&4095]=b
                if seed:initial[z&~4095][z&4095]=b
        def get(a,n=4):
            for k in range(n):ensure(a+k)
            return int.from_bytes(bytes(memory[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
        def store(a,v,n=4):expected.append((a&mask,n,v&((1<<(8*n))-1)));put(a,v,n)
        line=0x680101+align;record=0x690101+align;vbase=0x620001+align;sbase=0x600001+align
        if mode==1:record=line-2 # first pointer store overwrites second raw vertex index
        if mode==2:line=0x2c138 # vertex global overwritten, retained register base must survive
        if mode==3:vbase=line # x-delta store can change later coordinate reads
        if mode==4:vbase=line+30 # low bound aliases coordinate reloads
        if mode==5:vbase=line+34 # x minimum store aliases x1
        if mode==6:vbase=line+26 # y maximum overlaps an endpoint
        if mode==7:line=0xffffffdc # selected bound/pointer addresses wrap
        if mode==8:record=0xffffffff # first raw vertex word wraps
        fi,bi,fs,bs=(data['lines'][wad_id][2:6] if wad_id>=0 else (0,1,3,7))
        counter=wad_id if wad_id>=0 else (0xffffffff if case%2 else 474)
        put(0x2c138,vbase,seed=True);put(0x2c118,sbase,seed=True);put(0x2c134,475,seed=True)
        put(record,i,2,True);put(record+2,j,2,True);put(record+10,fi,2,True);put(record+12,bi,2,True)
        put(vbase+8*s16(i),x1,seed=True);put(vbase+8*s16(i)+4,y1,seed=True)
        put(vbase+8*s16(j),x2,seed=True);put(vbase+8*s16(j)+4,y2,seed=True)
        put(sbase+18*s16(fi)+14,0x610001+86*fs,seed=True)
        if bi!=65535:put(sbase+18*s16(bi)+14,0x610001+86*bs,seed=True)
        rr=[rng.getrandbits(32) for _ in regs];rr[1]=record;rr[3]=line;rr[5]=counter;before=rr.copy()
        # Vertex global read precedes the first pointer store and is reused.
        off1=(s16(get(record,2))*8)&mask;base=get(0x2c138);rr[6]=(base+off1)&mask;store(line,rr[6])
        off2=(s16(get(record+2,2))*8)&mask;rr[0]=(base+off2)&mask;store(line+4,rr[0]);rr[7]=rr[0]
        xx=(get(rr[7])-get(rr[6]))&mask;store(line+8,xx)
        rr[2]=get(rr[6]+4);rr[0]=(get(rr[7]+4)-rr[2])&mask;store(line+12,rr[0])
        def map_new():
            for a,b in initial.items():
                if a not in mapped:em.mem_map(a,4096);mapped.add(a);em.mem_write(a,bytes(b))
        def check(label,count,endpoint,known_flags=None):
            require(writes==expected,f'{label} writes/{case}')
            require([em.reg_read(r) for r in regs]==rr,f'{label} registers/{case}')
            require(all(bytes(em.mem_read(a,4096))==b for a,b in memory.items()),f'{label} memory/{case}')
            require(em.reg_read(x.UC_X86_REG_EIP)==CODE+endpoint and len(visits)==count,f'{label} endpoint/count/{case}')
            if known_flags is not None:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c0==known_flags,f'{label} flags/{case}')
        map_new()
        for r,v in zip(regs,before):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
        em.emu_start(CODE+0x2e2b2,CODE+0x2e2ec,count=19);check('prefix',18,0x2e2ec)
        if wad_id>=0:
            require([v for _,_,v in writes]==[vbase+8*i,vbase+8*j,(x2-x1)&mask,(y2-y1)&mask],f'WAD geometry/{case}')
        # New local entry after the unproved slope-classification gap.
        expected.clear();steps=10
        for off,lo,hi in [(0,34,38),(4,30,26)]:
            a=get(rr[6]+off);b=get(rr[7]+off);ge=s32(a)>=s32(b)
            store(line+lo,b if ge else a)
            rr[2]=b;rr[0]=get((rr[6] if ge else rr[7])+off);store(line+hi,rr[0]);steps+=7 if ge else 8
        bounds_values=[get(line+off) for off in [34,38,30,26]]
        for src,dst in [(10,22),(12,24)]:
            v=get(record+src,2);rr[0]=(rr[0]&0xffff0000)|v;store(line+dst,v,2)
        for src,dst in [(22,46),(24,50)]:
            v=get(line+src,2);rr[0]=s16(v)&mask
            if v==65535:val=0;steps+=4
            else:rr[2]=get(0x2c118);rr[0]=get(rr[2]+18*s16(v)+14);val=rr[0];steps+=8
            store(line+dst,val)
        rr[6]=get(0x2c134);rr[5]=(rr[5]+1)&mask;rr[1]=(rr[1]+14)&mask;rr[3]=(rr[3]+62)&mask
        endpoint=0x2e29a if s32(rr[5])<s32(rr[6]) else 0x2e3c1
        diff=(rr[5]-rr[6])&mask;of=((rr[5]^rr[6])&(rr[5]^diff))>>31
        flags=(0x40 if diff==0 else 0)|(0x80 if diff>>31 else 0)|(0x800 if of else 0)
        map_new();writes.clear();visits.clear()
        em.emu_start(CODE+0x2e326,CODE+0x2e3c1,count=43);check('suffix',steps,endpoint,flags)
        require([get(line+off) for off in [34,38,30,26]]==bounds_values,'bounds overwritten')
        if wad_id>=0:
            require(bounds_values==[min(x1,x2,key=s32),max(x1,x2,key=s32),min(y1,y2,key=s32),max(y1,y2,key=s32)],f'WAD bounds/{case}')
    return dict(cases=len(cases),segment_executions=2*len(cases),wad_lines=len(data['lines']),edge_cases=len(cases)-len(data['lines']),
        all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,signed_geometry=True,aliasing_and_wrapping=True,
        scope='Two separate local segments per case on synthetic layouts. The slope/FixedDiv gap is not executed; not full loader startup.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for name in ['original-line-geometry','original-line-load','original-line-cache']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wad_profile=geometry_data();require(profile['exe_sha256']==wad_profile['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-line-geometry';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineGeometry'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wad_profile['wad_sha256'],
        audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
        scope='Separate original vertex/delta prefix and bounds-to-advance suffix. Metadata, slope/FixedDiv gap, allocation and complete loader remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original vertex/delta prefix and bounds-through-loader suffix, with preserved grouping inputs.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Original complete scan establishes ordered E1M1 sector-array representation."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_original_noise_topology as topology
import verify_original_group_scan as scan
ROOT,require=extraction.ROOT,extraction.require
NAMES=[n+'_checked' for n in scan.UNITS]+['program_checked','ranges_checked','grouped_checked','sector_checked']
NAMES+=['Doom.Proofs.OriginalGroupFrame.'+n for n in ['helper_frame','continuation_frame','iteration_frame','iteration_written','scan_after']]
NAMES+=['Doom.Proofs.OriginalGroupOutput.'+n for n in ['inputs_step','output_and_frame','scan_output','stored_get','stored_rep','entry_rep']]
NAMES+=['Doom.Proofs.E1M1GroupOutput.'+n for n in ['physical_chosen','ordered_row','sector_rep']]
def certificate(raw,data):
    s=scan.certificate(raw).split('theorem scan_checked',1)[0]
    s=s.replace('import Doom.Proofs.OriginalGroupScan','import Doom.Proofs.E1M1GroupOutput').replace('ExtractedGroupScan','ExtractedGroupOutput')
    s+='open E1M1NoiseTopology E1M1GroupOutput\n'
    emitted=topology.certificate(data)
    s+='def topology : Topology := '+emitted.split('def topology : Topology := ',1)[1].split('theorem topology_checked',1)[0]
    s+='''theorem ranges_checked : ∀ e∈topology.lines, OriginalGroupLines.InRange e topology.sectors.length := by decide +kernel
theorem grouped_checked : topology.Grouped := by decide +kernel
theorem sector_checked (a : Addresses)
    (addresses : OriginalGroupLines.SectorAddresses a topology.sectors.length)
    (i : Fin topology.sectors.length) (s : X86Memory.State) (f : Option Flags)
    (setup : Setup topology a i s) :
    ∃ out, X86Routine.run extracted [0x2e6af] (6+43*topology.lines.length) ⟨s,f,0x2e661⟩=some out ∧
      out.pc=0x2e6af ∧ E1M1NoiseMap.Rep ⟨a.sector i.val,a.array i.val,(topology.sectors[i.val]).map a.line⟩ out.core.memory := by
  rw [program_checked]
  exact sector_rep topology a addresses ranges_checked grouped_checked i s f setup (by decide +kernel)
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedGroupOutput\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedGroupOutput.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,data):
    """Run every pinned E1M1 sector scan using its actual topology at a synthetic
    separated layout. Geometry is generated; the comparison is to WAD row order,
    not a captured execution trace or the Lean model's predicted output list."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x47585);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for n,pc in scan.UNITS.items():em.mem_write(CODE+pc,raw[n])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    blocks={0x2c000:4096,0x600000:0x30000}
    for a,n in blocks.items():em.mem_map(a,n)
    writes=[];steps=0
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        nonlocal steps
        if a==CODE+0x2e6af:e.emu_stop()
        else:steps+=1
    em.hook_add(u.UC_HOOK_CODE,visit)
    def signed(v):return v if v<0x80000000 else v-0x100000000
    total=len(data['lines']);pointers=0;largest=0
    for sector_id,row in enumerate(data['rows']):
        sp=0x600801;array=0x618001;linebase=0x601001;sector=0x620001+128*sector_id
        memory={a:bytearray(rng.randbytes(n)) for a,n in blocks.items()}
        def put(a,v):
            for start,buf in memory.items():
                if start<=a and a+4<=start+len(buf):buf[a-start:a-start+4]=(v&mask).to_bytes(4,'little');return
            raise ValueError('unmapped model write')
        def get(a):
            for start,buf in memory.items():
                if start<=a and a+4<=start+len(buf):return int.from_bytes(buf[a-start:a-start+4],'little')
            raise ValueError('unmapped model read')
        box=[0x80000000,0x7fffffff,0x7fffffff,0x80000000]
        for k,v in enumerate(box):put(sp+4*k,v)
        put(0x2c120,linebase);put(0x2c134,total);put(sector+78,len(row))
        vertices={}
        for index,flags,front_side,back_side,front,back in data['lines']:
            line=linebase+62*index;vertex=0x610001+16*index
            put(line,vertex);put(line+4,vertex+8)
            put(line+46,0x620001+128*front);put(line+50,0 if back_side==65535 else 0x620001+128*back)
            values=[rng.getrandbits(32) for _ in range(4)];vertices[index]=values
            for k,v in enumerate(values):put(vertex+4*k,v)
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=sp;rr[5]=sector;rr[6]=array
        for a,buf in memory.items():em.mem_write(a,bytes(buf))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps=0
        em.emu_start(CODE+0x2e661,CODE+0x2e6af,count=6+43*total+1)
        expected=[]
        def store(a,v):put(a,v);expected.append((a,4,v&mask))
        store(sector+82,array)
        for k,index in enumerate(row):
            store(array+4*k,linebase+62*index)
            xy=vertices[index]
            for j in [0,1]:
                store(sp-4,CODE+(0x2e690 if j==0 else 0x2e6a2))
                vx,vy=xy[2*j:2*j+2]
                if signed(vx)<signed(box[2]):box[2]=vx;store(sp+8,vx)
                elif signed(vx)>signed(box[3]):box[3]=vx;store(sp+12,vx)
                if signed(vy)<signed(box[1]):box[1]=vy;store(sp+4,vy)
                elif signed(vy)>signed(box[0]):box[0]=vy;store(sp,vy)
        actual_rows=[int.from_bytes(em.mem_read(array+4*k,4),'little') for k in range(len(row))]
        require(actual_rows==[linebase+62*i for i in row],f'ordered WAD row {sector_id}')
        require(writes==expected,f'ordered writes {sector_id}')
        rr[0]=total;rr[1]=linebase+62*total;rr[7]=total;rr[6]=array+4*len(row);rr[3]=total
        if row:rr[2],rr[3]=vertices[row[-1]][2:]
        require([em.reg_read(r) for r in regs]==rr,f'all registers {sector_id}')
        require(all(bytes(em.mem_read(a,len(buf)))==buf for a,buf in memory.items()),f'memory frame {sector_id}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,f'final flags {sector_id}')
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2e6af and steps<=6+43*total,f'endpoint/bound {sector_id}')
        pointers+=len(row);largest=max(largest,steps)
    return dict(sectors=len(data['rows']),lines_per_scan=total,iterations=len(data['rows'])*total,ordered_pointers=pointers,
        largest_instruction_count=largest,all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,
        scope='All pinned E1M1 sector rows at a synthetic separated layout with generated coordinates; not actual DOS startup allocation.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for name in ['original-group-lines','original-group-bounds']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wad_profile=topology.pinned_data();require(profile['exe_sha256']==wad_profile['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-group-output';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1GroupOutput'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wad_profile['wad_sha256'],audited_declarations=len(NAMES),
        sectors=len(data['rows']),lines=len(data['lines']),axioms=r.stdout.splitlines(),cross_check=native,
        scope='Original complete scan establishes one sector Rep with ordered WAD entries under explicit pre-state/layout relations; counting pass, allocator and whole-map startup remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original complete scan establishes ordered sector-array representation for pinned E1M1.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Whole original linedef loop, with explicit layout and arithmetic obligations."""
import argparse,json,re,subprocess
import verify_original_line_iteration as iteration
ROOT,require=iteration.ROOT,iteration.require
NAMES=[n if '.' in n else 'Doom.Verification.ExtractedLineIteration.'+n for n in iteration.NAMES]
NAMES+=['Doom.Proofs.E1M1LineFrame.'+n for n in ['result_eq','prepared_reg','selected_reg','division_bp','before_reg','before_stack','progress','prepared_frame','before_frame','frame','exit_pc','half_frame']]
NAMES+=['Doom.Proofs.E1M1LineScan.'+n for n in ['ready_step','states_ready','scan_path','scan_execution','e1m1_scan','suffix_frame']]
NAMES+=['Doom.Verification.ExtractedLineScan.scan_checked']
def certificate(raw,data):
    s=iteration.certificate(raw,data).replace('import Doom.Proofs.E1M1LineIteration','import Doom.Proofs.E1M1LineScan')
    s+='''namespace Doom.Verification.ExtractedLineScan
open Doom.Proofs X86 X86Memory X86Control ExtractedLineIteration
 theorem scan_checked {raw line sp s f} (layout : E1M1LineScan.Layout 475 line sp)
    (initial : E1M1LineScan.Ready 475 raw line sp 0 s)
    (arithmetic : E1M1LineScan.Arithmetic 475 s f) :
    X86Routine.run program [0x2e3c1] 49400 ⟨s,f,0x2e29a⟩=some (E1M1LineScan.states s f 475) ∧
    (E1M1LineScan.states s f 475).pc=0x2e3c1 ∧
    E1M1LineScan.Ready 475 raw line sp 475 (E1M1LineScan.states s f 475).core := by
  unfold program
'''
    s+='  rw ['+','.join(n+'_checked' for n in iteration.UNITS)+']\n'
    s+='  exact E1M1LineScan.e1m1_scan (raw:=raw) (line:=line) (sp:=sp) (s:=s) (f:=f) layout initial arithmetic\n'
    s+='\n'.join('#print axioms '+n for n in NAMES[len(iteration.NAMES):])
    return s+'\nend Doom.Verification.ExtractedLineScan\n'

def audit(output):
    rest=output.strip()
    for name in NAMES:
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,data):
    """Uninterrupted 475-record execution on synthetic layouts. Independently
    calculate every initialized record byte, retain padding and all source bytes.
    Stack write values were checked by the individual FixedDiv/iteration harness;
    here the full loop checks stack footprint and restoration, not stale values."""
    import random,struct
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e3c1);CODE=0x100000;DATA=0x600000;SIZE=0x60000;MASK=0xffffffff
    starts=[0x1d180,0x2e29a,0x2e2ec,0x2e2b2,0x2e2d6,0x2e326,0x2e33d,0x2e358,0x2e368,0x2e3ac]
    counts=[]
    def signed(v):return v if v<0x80000000 else v-0x100000000
    for case in range(5):
        em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
        for name,pc in zip(iteration.UNITS,starts):em.mem_write(CODE+pc,raw[name])
        em.mem_map(0x20000,0x10000);em.mem_map(DATA,SIZE)
        record=DATA+1+case%4;line=DATA+0x10003+case%4
        vertex=DATA+0x20001+case%4;side=DATA+0x30003+case%4
        sp=DATA+0x50005+case%4
        if case==4:
            sp=2;em.mem_map(0xfffff000,4096);em.mem_map(0,4096)
        initial=bytearray(rng.randbytes(SIZE));expected=initial.copy()
        def seed(a,v,n=4):
            initial[a-DATA:a-DATA+n]=(v&((1<<(8*n))-1)).to_bytes(n,'little')
        meta=[]
        for k,(a,b,x1,y1,x2,y2) in enumerate(data['geometry']):
            _,_,fi,bi,fs,bs=data['lines'][k]
            flags,special,tag=[rng.getrandbits(16) for _ in range(3)];meta.append((flags,special,tag))
            initial[record-DATA+14*k:record-DATA+14*k+14]=struct.pack('<7H',a,b,flags,special,tag,fi,bi)
            for idx,xx,yy in [(a,x1,y1),(b,x2,y2)]:seed(vertex+8*idx,xx);seed(vertex+8*idx+4,yy)
            if fi!=65535:seed(side+18*fi+14,DATA+0x40001+86*fs)
            if bi!=65535:seed(side+18*bi+14,DATA+0x40001+86*bs)
        expected=initial.copy()
        for k,(a,b,x1,y1,x2,y2) in enumerate(data['geometry']):
            _,_,fi,bi,fs,bs=data['lines'][k];dx=(x2-x1)&MASK;dy=(y2-y1)&MASK
            # E1M1 coordinate deltas fit this signed division; use its exact
            # fixed-point quotient sign, retaining zero's negative-slope branch.
            if dx==0:slope=1
            elif dy==0:slope=0
            else:
                aa,bb=abs(signed(dy)),abs(signed(dx))
                if aa>>14>=bb:q=-0x80000000 if signed(dy)^signed(dx)<0 else 0x7fffffff
                else:q=(aa*65536//bb)*(-1 if (signed(dy)<0)!=(signed(dx)<0) else 1)
                slope=3 if q<=0 else 2
            p=line-DATA+62*k
            def put(off,v,n=4):expected[p+off:p+off+n]=(v&((1<<(8*n))-1)).to_bytes(n,'little')
            for off,v in [(0,vertex+8*a),(4,vertex+8*b),(8,dx),(12,dy),
                (26,max(y1,y2,key=signed)),(30,min(y1,y2,key=signed)),
                (34,min(x1,x2,key=signed)),(38,max(x1,x2,key=signed)),(42,slope),
                (46,0 if fi==65535 else DATA+0x40001+86*fs),(50,0 if bi==65535 else DATA+0x40001+86*bs)]:put(off,v)
            for off,v in zip([16,18,20,22,24],[*meta[k],fi,bi]):put(off,v,2)
        em.mem_write(DATA,bytes(initial))
        for addr,val in [(0x2c134,475),(0x2c138,vertex),(0x2c118,side)]:em.mem_write(addr,val.to_bytes(4,'little'))
        globals_before=bytes(em.mem_read(0x20000,0x10000));visits=[];stack_bytes=set()
        for off in [4,8,12,16]:stack_bytes.update((sp-off+j)&MASK for j in range(4))
        def writing(_e,_a,addr,n,value,_d):
            if all(((addr+j)&MASK) in stack_bytes for j in range(n)):
                if DATA<=addr and addr+n<=DATA+SIZE:expected[addr-DATA:addr-DATA+n]=(value&((1<<(n*8))-1)).to_bytes(n,'little')
            else:require(line<=addr and addr+n<=line+62*475,'write escaped output and stack')
        em.hook_add(u.UC_HOOK_MEM_WRITE,writing)
        em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
        for r,v in [(x.UC_X86_REG_ECX,record),(x.UC_X86_REG_EBX,line),(x.UC_X86_REG_ESP,sp),(x.UC_X86_REG_EBP,0)]:em.reg_write(r,v)
        em.emu_start(CODE+0x2e29a,CODE+0x2e3c1,count=49401)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+0x2e3c1,'wrong final PC')
        require(visits.count(0x2e29a)==475 and len(visits)<=49400,'wrong loop count/fuel')
        require(em.reg_read(x.UC_X86_REG_ECX)==record+14*475,'raw cursor')
        require(em.reg_read(x.UC_X86_REG_EBX)==line+62*475,'line cursor')
        require(em.reg_read(x.UC_X86_REG_EBP)==475 and em.reg_read(x.UC_X86_REG_ESP)==sp,'counter/stack')
        require(bytes(em.mem_read(DATA,SIZE))==expected,'record/source/padding memory mismatch')
        require(bytes(em.mem_read(0x20000,0x10000))==globals_before,'global memory changed')
        counts.append(len(visits))
    return dict(loops=5,iterations=2375,instruction_counts=counts,wrapping_stack=True,
        initialized_records_and_padding=True,source_memory_unchanged=True,globals_unchanged=True,
        scope='Uninterrupted original loop on synthetic layouts; not actual DOS startup, nor a universal equivalence proof.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    extraction=iteration.extraction
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile);raw={}
    for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
        raw.update(extraction.extract(binary,profile,json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())))
    data,wp=iteration.setup.geometry.geometry_data();require(profile['exe_sha256']==wp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/original-line-scan';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineScan'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate(raw,data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw,data) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],wad_sha256=wp['wad_sha256'],audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),cross_check=native,
        scope='Positive-count loop from 0x2e29a to 0x2e3c1; explicit finite layout, initial count/cursors and per-iteration arithmetic safety. Actual startup memory and WAD-to-loaded-delta safety relation remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original whole linedef loop and suffix memory preservation.')
if __name__=='__main__':main()

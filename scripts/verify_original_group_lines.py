#!/usr/bin/env python3
"""Verify original P_GroupLines selection, stores and pinned E1M1 ordering rule."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
ROOT,require=extraction.ROOT,extraction.require
import verify_original_noise_topology as topology
NAMES=['group_checked','joined_checked','ranges_checked','grouped_checked','ordered_checked','line_checked']
NAMES+=['Doom.Proofs.OriginalGroupLines.'+n for n in ['decoded','entry_execution','selection_execution','entry_patch','entry_pointer','selection_patch','selected_pointer','joined_execution','selection_rule','ordered_selection','line_correspondence']]
def certificate(raw,data):
    s='''import Doom.Proofs.OriginalGroupLines
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.ExtractedGroupLines
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalGroupLines E1M1NoiseTopology
'''
    s+='def group : List UInt8 := ['+','.join(hex(v) for v in raw['group'])+']\n'
    s+='theorem group_checked : group=groupBytes := by decide +kernel\n'
    s+='''theorem joined_checked (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run (bytesProgram group) [0x2e682,0x2e6a2,0x2e6af] 11 ⟨s,f,0x2e661⟩=some (result s) := by
  rw [group_checked]; exact joined_execution s f
'''
    s+='''theorem line_checked (s : X86Memory.State) (f : Option Flags)
    (a : Addresses) (n : Nat) (layout : SectorAddresses a n) (e : Line)
    (valid : InRange e n) (i : Nat) (inside : i<n)
    (sector : s.regs 5=a.sector i) (line : s.regs 1=a.line e.index)
    (frontRead : front s=a.sector e.front) (backRead : back s=backAddress e a) :
    ∃ out, X86Routine.run program [0x2e682,0x2e6a2] 5 ⟨s,f,0x2e676⟩=some out ∧
      out.core.memory=E1M1NoiseImage.applyPatch
        (if e.front==i || (e.backIndex != 65535 && e.back==i) then E1M1NoiseImage.word (s.regs 6) (a.line e.index) else []) s.memory :=
  line_correspondence s f a n layout e valid i inside sector line frontRead backRead
'''
    # Reuse the pinned-WAD literal emitter; no WAD data enters tracked source.
    emitted=topology.certificate(data)
    s+='def topology : Topology := '+emitted.split('def topology : Topology := ',1)[1].split('theorem topology_checked',1)[0]
    s+='''theorem ranges_checked : ∀ e∈topology.lines, InRange e topology.sectors.length := by decide +kernel
theorem grouped_checked : topology.Grouped := by decide +kernel
theorem ordered_checked (a : Addresses) (layout : SectorAddresses a topology.sectors.length)
    (i : Fin topology.sectors.length) :
    (topology.lines.filter fun e => accepts (a.sector i.val) (a.sector e.front) (backAddress e a)).map Line.index=topology.sectors[i.val] :=
  ordered_selection topology a layout ranges_checked grouped_checked i
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedGroupLines\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedGroupLines.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Execute the original segment; preserve load/store order even under aliasing."""
    import random
    import unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e661);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    em.mem_write(CODE+0x2e661,raw['group'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    page_addrs=[0,0x2c000,0x600000,0xfffff000]
    for a in page_addrs:em.mem_map(a,4096)
    writes=[];visits=[];coverage=dict(empty=0,front=0,back=0,skip=0)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    def visit(e,a,_n,_d):
        if a-CODE in [0x2e682,0x2e6a2,0x2e6af]:e.emu_stop()
        else:visits.append(a-CODE)
    em.hook_add(u.UC_HOOK_CODE,visit)
    def cmpflags(a,b):
        d=(a-b)&mask
        return int(a<b)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    cases=0
    for mode in range(8):
        for count in [0,1,475,0x7fffffff,0x80000000,0xffffffff]:
            for branch in range(4):
                for align in range(4):
                    pages={a:bytearray(rng.randbytes(4096)) for a in page_addrs}
                    def put(a,v,n=4):
                        for k,b in enumerate((v&((1<<(8*n))-1)).to_bytes(n,'little')):
                            z=(a+k)&mask;pages[z&~4095][z&4095]=b
                    def get(a,n=4):return int.from_bytes(bytes(pages[((a+k)&mask)&~4095][((a+k)&mask)&4095] for k in range(n)),'little')
                    rr=[rng.getrandbits(32) for _ in regs];line=0x600201+align
                    rr[5]=0x600501+align;rr[6]=0x600901+align
                    if mode==1:rr[6]=mask
                    if mode==2:rr[5]=(mask-82)&mask
                    if mode==3:rr[5]=line+46-82
                    if mode==4:rr[5]=line+50-82
                    if mode==5:rr[5]=0x2c134-82
                    if mode==6:rr[5]=0x2c120-82
                    if mode==7:rr[6]=line+46
                    put(line+46,rr[5] if branch in [0,2] else 0x600700)
                    put(line+50,rr[5] if branch in [1,2] else 0)
                    put(0x2c120,line);put(0x2c134,count)
                    for a,b in pages.items():em.mem_write(a,bytes(b))
                    for r,v in zip(regs,rr):em.reg_write(r,v)
                    em.reg_write(x.UC_X86_REG_EFLAGS,2|(rng.getrandbits(12)&0x8d5));writes.clear();visits.clear()
                    em.emu_start(CODE+0x2e661,CODE+0x40000,count=12)
                    rr[7]=0;rr[1]=get(0x2c120);rr[3]=get(0x2c134)
                    dest=(rr[5]+82)&mask;put(dest,rr[6]);expected=[(dest,4,rr[6])];n=6
                    flags=(int(rr[3]==0)<<6)|((rr[3]>>31)<<7)
                    if rr[3]==0 or rr[3]>=0x80000000:pc=0x2e6af;coverage['empty']+=1
                    else:
                        front=get(rr[1]+46);flags=cmpflags(rr[5],front);n+=2
                        if rr[5]==front:hit=True;coverage['front']+=1
                        else:
                            back=get(rr[1]+50);flags=cmpflags(rr[5],back);n+=2
                            hit=rr[5]==back;coverage['back' if hit else 'skip']+=1
                        if hit:
                            put(rr[6],rr[1]);expected.append((rr[6],4,rr[1]));n+=1;pc=0x2e682
                        else:pc=0x2e6a2
                    require(writes==expected,f'ordered writes/{mode}/{count}/{branch}/{align}')
                    require([em.reg_read(r) for r in regs]==rr,'registers')
                    require(all(bytes(em.mem_read(a,4096))==b for a,b in pages.items()),'memory frame')
                    require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'modeled flags')
                    require(em.reg_read(x.UC_X86_REG_EIP)==CODE+pc and len(visits)==n,'endpoint/count')
                    cases+=1
    require(all(coverage.values()),'missing branch coverage')
    return dict(cases=cases,branches=coverage,all_registers=True,ordered_writes=True,mapped_memory_frame=True,modeled_flags=True,
        wrapping_unaligned_stores=True,aliased_publication_and_line_fields=True,
        scope='Local joined entry/selection executions; no bounding-box calls or complete scan.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-group-lines.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    out=ROOT/'artifacts/original-group-lines';out.mkdir(parents=True,exist_ok=True);(out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-side-loader')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupLines'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    data,wad_profile=topology.pinned_data()
    require(profile['exe_sha256']==wad_profile['exe_sha256'],'profile executable mismatch')
    path=out/'Checked.lean';path.write_text(certificate(raw,data))
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    native=cross_check(raw) if args.cross_check else None
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),
        wad_sha256=wad_profile['wad_sha256'],sectors=len(data['rows']),lines=len(data['lines']),axioms=r.stdout.splitlines(),cross_check=native,scope=spec['scope']),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original group-line entry/selection/store and pinned E1M1 ordered selection rule.')
if __name__=='__main__':main()

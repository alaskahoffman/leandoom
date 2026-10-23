#!/usr/bin/env python3
"""Authenticate collection-to-selector setup, count recovery and record framing."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_e1m1_intercept_gate as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={'OriginalInterceptSetup':['decoded','handoff_execution','prologue_execution','byte_distance','count_execution'],
        'E1M1InterceptSetup':['memory','frame','cursor_read','fields','execution','records'],
        'E1M1TraversalEntry':['contains_collection','contains_setup','from_collection','execution']}

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-intercept-setup.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate setup range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def certificate(data,raw):
    source='import Doom.Proofs.E1M1TraversalEntry\n'+previous.certificate(data,raw)
    source+='''
namespace Doom.Verification.ExtractedTraversalEntry
open Doom.Proofs X86 X86Memory X86Control
open E1M1InterceptSetup (Safe result)
'''
    for name,unit,const in [('setup','interceptSetup','setupCode'),('handoff','interceptHandoff','handoffCode')]:
        literal='['+','.join(hex(b) for b in raw[unit])+']'
        source+=f'def {name} : List UInt8 := {literal}\ntheorem {name}_checked : {name}=OriginalInterceptSetup.{const} := by decide\n'
    source+='''def program := OriginalInterceptSetup.bytesProgram setup handoff
theorem program_checked : program=OriginalInterceptSetup.program := by
  simp only [program,setup_checked,handoff_checked,OriginalInterceptSetup.program]
theorem execution_checked (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (bound : n≤128) (limit : load32 s.memory 0x2c028=E1M1MinimumScan.address n)
    (safe : Safe (s.regs 4) 0x2c028) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 23 ⟨s,f,0x2cafd⟩ (result s n) := by
  rw [program_checked]
  exact E1M1InterceptSetup.execution s f n bound limit safe
#print axioms setup_checked
#print axioms handoff_checked
#print axioms program_checked
#print axioms execution_checked
end Doom.Verification.ExtractedTraversalEntry
'''
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedTraversalEntry.setup_checked'"
    require(marker in output,'missing setup audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedTraversalEntry.'+n for n in ['setup_checked','handoff_checked','program_checked','execution_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,count=516):
    """Diagnostic execution of the real caller and setup, without callback stubs."""
    import random,struct,capstone
    import unicorn as u
    from unicorn import x86_const as x
    for name,start,n in [('interceptHandoff',0x2cafd,3),('interceptSetup',0x2c810,20)]:
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],start))
        require(b''.join(bytes(i.bytes) for i in listing)==raw[name] and len(listing)==n,'decoder mismatch')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0,0x50000);em.mem_map(0x100000,0x50000)
    em.mem_write(0x100000+0x2cafd,raw['interceptHandoff']);em.mem_write(0x100000+0x2c810,raw['interceptSetup'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *args:writes.append((args[2],args[3],args[4])))
    em.hook_add(u.UC_HOOK_CODE,lambda *args:visits.append(args[1]))
    rng=random.Random(0x2c810);pack=lambda v:struct.pack('<I',v)
    groups=dict(empty=0,nonempty=0,capacity=0)
    for case in range(count):
        n=case%129;before=[rng.getrandbits(32) for _ in regs];before[4]=0x40000
        callback=rng.getrandbits(32);limit=0x2ba20+12*n
        em.mem_write(0x40000+68,pack(callback));em.mem_write(0x2c028,pack(limit))
        records=rng.randbytes(128*12);em.mem_write(0x2ba20,records)
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        end=0x100000+(0x2c887 if n==0 else 0x2c841)
        em.emu_start(0x100000+0x2cafd,end,count=24)
        expected=[n,limit,0,0,0x40000-24,before[5],(n-1)&0xffffffff,65536]
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'setup exit mismatch')
        require([em.reg_read(reg) for reg in regs]==expected,'setup register mismatch')
        require(len(visits)==23,'setup instruction count mismatch')
        require(writes==[(0x40000-4,4,0x12cb0b),(0x40000-8,4,before[3]),
          (0x40000-12,4,before[1]),(0x40000-16,4,before[6]),(0x40000-20,4,before[7]),
          (0x40000-24,4,callback)],'setup memory writes mismatch')
        require(bytes(em.mem_read(0x2ba20,len(records)))==records,'setup changed records')
        require(bytes(em.mem_read(0x2c028,4))==pack(limit),'setup changed cursor')
        groups['empty']+=n==0;groups['nonempty']+=n>0;groups['capacity']+=n==128
    require(all(groups.values()),'missing setup edge cases')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,distinct_counts=min(count,129),code_origin=0x100000)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-traversal-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1TraversalEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous query entry through collection and real selector call/prologue/count setup, preserving full records under static stack separation. '
      'Empty collections bypass the scan; nonempty collections reach the previously proved scan entry. '
      'New DEC ESI decoding reuses wrapping add-immediate semantics with flags invalidated until the following TEST. '
      'Callback clipping, encoded sentinel updates, repeated processing and query return remain open. '
      'Existing reachability contracts remain; runtime game code unchanged.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: query collection joined to original selector setup; strict transitive axiom audit.')
if __name__=='__main__':main()

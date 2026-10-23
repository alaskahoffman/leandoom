#!/usr/bin/env python3
"""Certify original strict-min intercept selection against the live source."""
import argparse
import json
import verify_original_inline_thrust as extraction
import re
import subprocess
import verify_e1m1_query_collection as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalInterceptMinimum': ['decoded', 'iteration', 'entry_execution', 'fields'],
          'E1M1InterceptMinimum': ['live', 'replay', 'minimum_replay', 'tie', 'minimum_none'],
          'E1M1MinimumScan': ['address_next', 'address_value', 'fractions', 'next', 'next_pc', 'scan', 'execution']}
pinned_data = previous.pinned_data


def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-intercept-minimum.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not (set(part['units']) & set(spec['units'])),'duplicate minimum range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1MinimumScan\n'+previous.certificate(data,raw)
    literal='['+','.join(hex(b) for b in raw['interceptMinimum'])+']'
    source += f"""
namespace Doom.Verification.ExtractedInterceptMinimum
open Doom.Proofs X86 X86Memory X86Control
 def bytes : List UInt8 := {literal}
 theorem bytes_checked : bytes=OriginalInterceptMinimum.code := by decide
 theorem execution_checked (s : X86Memory.State) (f : Option Flags)
     (hits : Array Doom.Collision.Intercept) (bounded : hits.size≤128)
     (limit : s.regs 1=E1M1MinimumScan.address hits.size)
     (encoded : E1M1MinimumScan.Fractions s.memory hits) :
     ∃ n≤4+7*hits.size, ∃ out best,
       X86CodeMemory.Prefix FloorCaller.cm (OriginalInterceptMinimum.bytesProgram bytes) [] n
         ⟨s,f,0x2c841⟩ out ∧ E1M1InterceptMinimum.minimum hits=.ok best ∧
       E1M1MinimumScan.Represents out.core hits hits.size best ∧ out.pc=0x2c85e ∧ out.core.memory=s.memory := by
   rw [bytes_checked]; exact E1M1MinimumScan.execution s f hits bounded limit encoded
 #print axioms bytes_checked
 #print axioms execution_checked
end Doom.Verification.ExtractedInterceptMinimum
"""
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Verification.ExtractedInterceptMinimum.bytes_checked'"
    require(marker in output,'missing minimum scan audit')
    before,rest=output.split(marker,1)
    previous.audit(before)
    rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedInterceptMinimum.bytes_checked',
           'Doom.Verification.ExtractedInterceptMinimum.execution_checked']
    names += ['Doom.Proofs.'+module+'.'+name for module,group in GROUPS.items() for name in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(code, count=512):
    """Independent execution of extracted x86 bytes; diagnostic, not a proof."""
    import random
    import struct
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    require(count>=128,'too few minimum scan cases')
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,0x2c841))
    require(b''.join(bytes(i.bytes) for i in listing)==code and len(listing)==11,'decoder mismatch')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(0,0x30000);em.mem_map(0x100000,0x50000)
    em.mem_write(0x100000+0x2c841,code)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *args:writes.append(args[2]))
    def hook(emu,a,size,data):
        if a==0x100000+0x2c85e:emu.emu_stop()
        else:visits.append(a)
    em.hook_add(u.UC_HOOK_CODE,hook)
    rng=random.Random(0x2c841)
    signed=lambda v:v if v<2**31 else v-2**32
    edges=[0,1,65535,65536,65537,0x7fffffff,0x80000000,0xffffffff]
    groups=dict(empty=0,sentinel_only=0,ties=0,negative=0,capacity=0)
    for case in range(count):
        n=case%129
        values=[rng.choice(edges) if case%2 else rng.getrandbits(32) for _ in range(n)]
        if case%7==0:values=[0x7fffffff]*n
        if case%7==1:values=[65536]*n
        before=[rng.getrandbits(32) for _ in regs]
        before[1]=0x2ba20+12*n
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2)
        memory=b''.join(struct.pack('<III',v,rng.getrandbits(32),rng.getrandbits(32)) for v in values)
        if memory:em.mem_write(0x2ba20,memory)
        distance=0x7fffffff;choice=before[3];improvements=0
        for i,v in enumerate(values):
            if signed(v)<signed(distance):distance=v;choice=0x2ba20+12*i;improvements+=1
        expected=list(before);expected[0]=before[1];expected[2]=distance;expected[3]=choice
        writes.clear();visits.clear()
        em.emu_start(0x100000+0x2c841,0x100000+0x2c85e,count=4+7*n+1)
        require(em.reg_read(x.UC_X86_REG_EIP)==0x100000+0x2c85e,'scan did not exit')
        require([em.reg_read(r) for r in regs]==expected,'minimum register mismatch')
        require(not writes,'minimum scan wrote memory')
        require(len(visits)==4+5*n+2*improvements,'instruction count mismatch')
        require(bytes(em.mem_read(0x2ba20,len(memory)))==memory if memory else True,'record mutation')
        groups['empty']+=n==0;groups['sentinel_only']+=n>0 and all(v==0x7fffffff for v in values)
        groups['ties']+=n>0 and values.count(distance)>1;groups['negative']+=any(v>=2**31 for v in values)
        groups['capacity']+=n==128
    require(all(groups.values()),'missing scan edge cases')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cross-check',action='store_true')
    args=parser.parse_args()
    data,map_profile=pinned_data()
    spec,profile,raw=extracted()
    require(profile['exe_sha256']==map_profile['exe_sha256'],'executable profile mismatch')
    out=ROOT/'artifacts/e1m1-minimum-scan'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1MinimumScan'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='One new authenticated DOS range: 0x2c841–0x2c85e. '
                      'For every encoded array of at most 128 records, original '
                      'scan execution agrees with the exact selector exposed '
                      'inside the live ordered-hit tail. Signed strict minimum, '
                      'first equal-distance choice, empty and sentinel-only '
                      'arrays are covered. A stale EBX is permitted when no '
                      'hit is selected. Prologue/count setup, distance gate, '
                      'callback execution, sentinel mutation/repeated passes '
                      'and full ordered traversal remain open, as does joining '
                      'this scan to query collection. Runtime and instruction '
                      'semantics are unchanged.')
    if args.cross_check:
        report['cross_check']=cross_check(raw['interceptMinimum'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original minimum scan matches the live selector; strict transitive axiom audit.')


if __name__=='__main__':main()

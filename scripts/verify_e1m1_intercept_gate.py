#!/usr/bin/env python3
"""Certify the original intercept distance, callback-call and resume branches."""
import argparse
import json
import re
import subprocess
import verify_original_inline_thrust as extraction
import verify_e1m1_minimum_scan as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={'OriginalInterceptGate':['decoded','gate_execution','call_execution','resume_execution'],
        'E1M1InterceptGate':['contains_scan','contains_gate','scan','gate_agrees','no_choice','execution','admitted','callback']}


def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-intercept-gate.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate gate range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw


def certificate(data,raw):
    source='import Doom.Proofs.E1M1InterceptGate\n'+previous.certificate(data,raw)
    literal='['+','.join(hex(b) for b in raw['interceptGate'])+']'
    source+=f'''
namespace Doom.Verification.ExtractedInterceptGate
open Doom.Proofs X86 X86Memory X86Control BlockSummary
open E1M1MinimumScan (address Fractions Represents)
open E1M1InterceptMinimum (minimum)
open OriginalInterceptGate (gate)
def bytes : List UInt8 := {literal}
theorem bytes_checked : bytes=OriginalInterceptGate.code := by decide
def linked : X86Routine.Program := fun pc =>
  if pc<0x2c85e then OriginalInterceptMinimum.bytesProgram ExtractedInterceptMinimum.bytes pc
  else OriginalInterceptGate.bytesProgram bytes pc
theorem linked_checked : linked=E1M1InterceptGate.program := by
  funext pc
  simp only [linked,bytes_checked,ExtractedInterceptMinimum.bytes_checked]
  rfl
'''
    text=(ROOT/'Doom/Proofs/E1M1InterceptGate.lean').read_text()
    start=text.index('theorem execution ')
    decl=text[start:text.index(' := by',start)]
    decl=decl.replace('theorem execution','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1InterceptGate.execution s f hits bounded limit encoded maximum\n'
    source+='\n'.join('#print axioms '+n for n in ['bytes_checked','linked_checked','execution_checked'])
    source+='\nend Doom.Verification.ExtractedInterceptGate\n'
    for module,names in GROUPS.items():
        source+='\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker="'Doom.Verification.ExtractedInterceptGate.bytes_checked'"
    require(marker in output,'missing gate audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedInterceptGate.'+n for n in ['bytes_checked','linked_checked','execution_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw,count=512):
    """Independent x86 execution, stopping at real callee entry (no stub)."""
    import random,struct
    import capstone
    import unicorn as u
    from unicorn import x86_const as x
    code=raw['interceptGate']
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,0x2c85e))
    require(b''.join(bytes(i.bytes) for i in listing)==code and len(listing)==12,'decoder mismatch')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    em.mem_map(0,0x50000);em.mem_map(0x100000,0x50000)
    em.mem_write(0x100000+0x2c841,raw['interceptMinimum']+code)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *args:writes.append((args[2],args[3],args[4])))
    rng=random.Random(0x2c85e);pack=lambda v:struct.pack('<I',v)
    signed=lambda v:v if v<2**31 else v-2**32
    groups=dict(rejected=0,admitted=0,endpoint=0,negative=0,sentinel=0,stop=0,resume=0)
    for case in range(count):
        n=case%129
        values=[rng.getrandbits(32) for _ in range(n)]
        if case%5==0:values=[65536]*n
        if case%5==1:values=[0x7fffffff]*n
        if case%5==2:values=[65537]*n
        before=[rng.getrandbits(32) for _ in regs]
        before[1]=0x2ba20+12*n;before[4]=0x40000;before[7]=65536
        em.mem_write(0x40000,pack(0x130000))
        em.mem_write(0x3fffc,pack(0xfeedface))
        memory=b''.join(struct.pack('<III',v,1,i) for i,v in enumerate(values))
        if memory:em.mem_write(0x2ba20,memory)
        for reg,v in zip(regs,before):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear()
        distance=0x7fffffff;choice=before[3]
        for i,v in enumerate(values):
            if signed(v)<signed(distance):distance=v;choice=0x2ba20+12*i
        rejected=signed(distance)>65536
        end=0x100000+0x2c887 if rejected else 0x130000
        em.emu_start(0x100000+0x2c841,end,count=4+7*n+6)
        expected=list(before);expected[0]=before[1] if rejected else choice
        expected[2]=distance;expected[3]=choice
        if not rejected:expected[4]-=4
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'wrong gate/call exit')
        require([em.reg_read(r) for r in regs]==expected,'gate/call registers differ')
        expected_writes=[(0x2c028,4,before[1])]
        if not rejected:expected_writes.append((0x3fffc,4,0x12c86d))
        require(writes==expected_writes,'gate/call writes differ')
        if memory:require(bytes(em.mem_read(0x2ba20,len(memory)))==memory,'gate changed records')
        groups['rejected']+=rejected;groups['admitted']+=not rejected
        groups['endpoint']+=distance==65536;groups['negative']+=signed(distance)<0
        groups['sentinel']+=distance==0x7fffffff
        # Separately execute from the real return site, with arbitrary returned
        # state. This does not stand in for, or claim to verify, the callback.
        returned=[rng.getrandbits(32) for _ in regs]
        returned[0]=0 if case%2==0 else rng.randrange(1,2**32)
        returned[3]=0x2ba20+12*(case%128);returned[4]=0x40000
        cursor=rng.getrandbits(32)
        em.mem_write(0x2c028,pack(cursor));em.mem_write(returned[3],pack(123))
        for reg,v in zip(regs,returned):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear()
        end=0x100000+(0x2c88c if returned[0]==0 else 0x2c83a)
        em.emu_start(0x100000+0x2c86d,end,count=6)
        expected=list(returned);expected[1]=cursor
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'wrong resume exit')
        require([em.reg_read(r) for r in regs]==expected,'resume registers differ')
        require(writes==([] if returned[0]==0 else [(returned[3],4,0x7fffffff)]),'resume writes differ')
        groups['stop']+=returned[0]==0;groups['resume']+=returned[0]!=0
    require(all(groups.values()),'missing gate edge cases')
    return dict(scan_gate_call_cases=count,post_callback_cases=count,groups=groups,callbacks_or_stubs=False,
                code_origin=0x100000,return_addresses_checked_with_code_origin=True)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,map_profile=pinned_data();spec,profile,raw=extracted()
    require(profile['exe_sha256']==map_profile['exe_sha256'],'executable profile mismatch')
    out=ROOT/'artifacts/e1m1-intercept-gate';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1InterceptGate'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Minimum scan continuously joined to signed inclusive 65536 distance gate. Admitted minima name real records; '
            'the real indirect call passes that pointer and pushes its return address. No-choice sentinel exits before the call. '
            'Both post-callback branches proved, including cursor reload and sentinel write only on nonzero return. '
            'Callback body, array encoding preservation after marking, repeated passes, prologue and collection handoff remain open. '
            'Entry contracts and existing x86 semantics remain explicit. Runtime unchanged.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: scan-to-distance gate, selected callback argument, and post-callback branches; strict axiom audit.')

if __name__=='__main__':main()

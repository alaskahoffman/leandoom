#!/usr/bin/env python3
"""Certify continuous query-to-first-intercept dispatch using existing DOS bytes."""
import argparse,json,re,subprocess
import verify_e1m1_traversal_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
GROUPS={'E1M1FirstIntercept':['contains_entry','contains_selection','contains_call','dispatch','empty_tail','rejected_tail'],
        'E1M1QueryDispatch':['execution']}

def certificate(data,raw):
    source='import Doom.Proofs.E1M1QueryDispatch\n'+previous.certificate(data,raw)
    source+='''
namespace Doom.Verification.ExtractedQueryDispatch
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs X86 X86Memory X86Control
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1TraversalEntry (Protected)
open E1M1FirstIntercept (Boundary)
def linked : X86Routine.Program := fun pc =>
  match E1M1TraversalEntry.program pc with
  | some op => some op
  | none => ExtractedInterceptGate.linked pc
theorem program_checked : linked=E1M1FirstIntercept.program := by
  exact congrArg
    (fun next : X86Routine.Program => fun pc =>
      match E1M1TraversalEntry.program pc with
      | some op => some op
      | none => next pc)
    ExtractedInterceptGate.linked_checked
'''
    text=(ROOT/'Doom/Proofs/E1M1QueryDispatch.lean').read_text();a=text.index('theorem execution ')
    decl=text[a:text.index(' := by',a)].replace('theorem execution','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [program_checked]\n  exact E1M1QueryDispatch.execution q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated room\n'
    source+='#print axioms program_checked\n#print axioms execution_checked\nend Doom.Verification.ExtractedQueryDispatch\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedQueryDispatch.program_checked'"
    require(marker in output,'missing dispatch audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedQueryDispatch.'+n for n in ['program_checked','execution_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,count=516):
    """Run caller + setup + first scan + distance gate + CALL without a stub."""
    import random,struct
    import unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0,0x50000);em.mem_map(0x100000,0x50000)
    for name,pc in [('interceptHandoff',0x2cafd),('interceptSetup',0x2c810),('interceptMinimum',0x2c841),('interceptGate',0x2c85e)]:
        em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
          x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4])))
    em.hook_add(u.UC_HOOK_CODE,lambda *a:visits.append(a[1]))
    rng=random.Random(0x2cb06);pack=lambda v:struct.pack('<I',v);signed=lambda v:v if v<2**31 else v-2**32
    groups=dict(empty=0,beyond=0,callback=0,endpoint=0,negative=0,ties=0,sentinel=0,capacity=0)
    for case in range(count):
        n=case%129;before=[rng.getrandbits(32) for _ in regs];before[4]=0x40000
        values=[rng.getrandbits(32) for _ in range(n)]
        if case%5==0:values=[65536]*n
        if case%5==1:values=[0x7fffffff]*n
        if case%5==2:values=[65537]*n
        callback=0x130000;limit=0x2ba20+12*n
        em.mem_write(0x40000+68,pack(callback));em.mem_write(0x2c028,pack(limit))
        records=b''.join(struct.pack('<III',v,1,i) for i,v in enumerate(values))+rng.randbytes((128-n)*12)
        em.mem_write(0x2ba20,records)
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        distance=0x7fffffff;choice=0;improvements=0
        for i,v in enumerate(values):
            if signed(v)<signed(distance):distance=v;choice=0x2ba20+12*i;improvements+=1
        calling=n>0 and signed(distance)<=65536
        end=callback if calling else 0x100000+0x2c887
        em.emu_start(0x100000+0x2cafd,end,count=33+7*n)
        expected=[0 if n==0 else choice if calling else limit,limit,0 if n==0 else distance,
                  choice if n else 0,0x40000-24-(4 if calling else 0),before[5],(n-1)&0xffffffff,65536]
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'dispatch exit mismatch')
        require([em.reg_read(reg) for reg in regs]==expected,'dispatch registers mismatch')
        expected_steps=23+(4+5*n+2*improvements+3+(2 if calling else 0) if n else 0)
        require(len(visits)==expected_steps,'dispatch instruction count mismatch')
        expected_writes=[(0x40000-4,4,0x12cb0b),(0x40000-8,4,before[3]),(0x40000-12,4,before[1]),
                         (0x40000-16,4,before[6]),(0x40000-20,4,before[7]),(0x40000-24,4,callback)]
        if n:expected_writes.append((0x2c028,4,limit))
        if calling:expected_writes.append((0x40000-28,4,0x12c86d))
        require(writes==expected_writes,'dispatch memory writes mismatch')
        require(bytes(em.mem_read(0x2ba20,len(records)))==records,'dispatch changed records')
        groups['empty']+=n==0;groups['beyond']+=n>0 and not calling;groups['callback']+=calling
        groups['endpoint']+=n>0 and distance==65536;groups['negative']+=n>0 and signed(distance)<0
        groups['ties']+=n>0 and values.count(distance)>1;groups['sentinel']+=n>0 and distance==0x7fffffff;groups['capacity']+=n==128
    require(all(groups.values()),'missing first-dispatch edge cases')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,distinct_counts=min(count,129),code_origin=0x100000,
                scope='Collection exit through first dispatch only; query collection itself is covered by the kernel theorem, not this diagnostic.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-query-dispatch';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1QueryDispatch'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous original query entry through initialization, collection, selector setup and first scan/cutoff to no-hit exit or indirect callback entry. '
      'Callback argument matches the exact live source minimum and is in bounds. Empty and out-of-range source tails return unchanged for any visitor. '
      'Existing entry contracts remain; callback target identity, callee body/clipping, record preservation after the final stores, repeated passes and return remain open. '
      'No runtime, decoder or instruction-semantics change; no new byte ranges.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: continuous query-to-first-dispatch proof and exact no-hit source tails; strict axiom audit.')
if __name__=='__main__':main()

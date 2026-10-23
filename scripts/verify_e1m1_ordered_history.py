#!/usr/bin/env python3
"""Authenticate ordered-history induction and the original traversal budget."""
import argparse,json,re,subprocess
import verify_e1m1_aim_repeat as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1OrderedVisit':['live','replay','live_walk'],
 'E1M1SelectionHistory':['scan_value','selected_value','initial_image','mark_image','fresh','image','distinct','count','original_log','same_count'],
 'E1M1OrderedTraversal':['continue_step','stop_step','range_step','traversal','live_history'],
 'E1M1TraversalBudget':['capacity','remaining_step','callback_index','head_budget','resumed_budget']}

def certificate(data,raw):
    source='import Doom.Proofs.E1M1TraversalBudget\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedOrderedHistory\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory E1M1InterceptMinimum\nopen E1M1AimNextSelection (head)\n'
    for module,name,checked,args in [('E1M1OrderedTraversal','live_history','source_checked','initial visit'),('E1M1TraversalBudget','head_budget','counter_checked','s f initial work seen visits history bounded counter')]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['source_checked','counter_checked'])+'\nend Doom.Verification.ExtractedOrderedHistory\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedOrderedHistory.source_checked'"
    require(marker in output,'missing ordered history audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedOrderedHistory.'+n for n in ['source_checked','counter_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')



def cross_check(raw,count=256):
    """Complete repeated selection with actual open-line callbacks, no stubs.
    Equal-height sectors isolate ordering, sentinels and counter exhaustion.
    """
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    units=[('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340),('aimDistance',0x2b797),('aimFloor',0x2b7a6),('division',0x1d180),('aimCeiling',0x2b7d1),('aimWindow',0x2b800),('aimContinue',0x2b89d),('interceptSetup',0x2c810),('interceptMinimum',0x2c841),('interceptGate',0x2c85e)]
    for name,pc in units:em.mem_write(0x100000+pc,raw[name])
    rng=random.Random(0x5e1ec7);mask=0xffffffff;calls=[];steps=[]
    pack=lambda v:struct.pack('<I',v&mask)
    def word(a):return struct.unpack('<I',bytes(em.mem_read(a&mask,4)))[0]
    def hook(machine,address,size,data):
        if address in (0x12c887,0x12c88c):machine.emu_stop();return
        steps.append(address)
        if address==0x12b760:
            pointer=machine.reg_read(x.UC_X86_REG_EAX)
            require(pointer==machine.reg_read(x.UC_X86_REG_EBX),'callback argument mismatch')
            require((pointer-0x2ba20)%12==0,'unaligned callback record')
            j=(pointer-0x2ba20)//12
            require(0<=j<n,'out-of-bounds callback')
            require(machine.reg_read(x.UC_X86_REG_ESI)==n-len(calls)-1,'wrong remaining counter at callback')
            require(machine.reg_read(x.UC_X86_REG_ESP)==(sp-4)&mask,'wrong callback frame')
            require(word((sp-4)&mask)==0x12c86d,'wrong actual return site')
            calls.append(j)
    em.hook_add(u.UC_HOOK_CODE,hook)
    groups=dict(empty=0,exhausted=0,range_rejected=0,callback_stopped=0,full_buffer=0,ties=0,negative=0,wrapping_stack=0)
    total=0
    for case in range(count):
        n=[0,1,2,4,8,16,127,128][case%8];sp=[0x700800,0,4,16,32,0xfffffff0][(case//8)%6]
        closed=case%9==0
        fractions=[rng.choice([-2147483648,-1,0,1,65536,65537,2147483647]) for _ in range(n)]
        if case%5==0:fractions=[65536]*n
        if case%7==0:fractions=[2147483647]*n
        order=sorted((i for i in range(n) if fractions[i]<=65536),key=lambda i:(fractions[i],i))
        expected=order[:1] if closed else order
        records=[[f&mask,1,0x600200] for f in fractions]
        if n:em.mem_write(0x2ba20,b''.join(struct.pack('<III',*r) for r in records))
        em.mem_write(0x600210,b'\x04');em.mem_write(0x600218,b'\x00\x00')
        for addr,val in [(0x60022e,0x600300),(0x600232,0x600400),(0x600300,0),(0x600304,128*65536),(0x600400,0),(0x600404,128*65536),(0x2b9b8,65536),(0x2b9a8,32*65536),(0x2c1e4,0),(0x2c1e8,0 if closed else 100),(sp,0x12b760),(0x2c028,0x2ba20+12*n)]:em.mem_write(addr,pack(val))
        regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
        initial=[rng.getrandbits(32) for _ in regs];initial[1]=0x2ba20+12*n;initial[4]=sp;initial[6]=n;initial[7]=65536
        for reg,val in zip(regs,initial):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);calls.clear();steps.clear()
        em.emu_start(0x12c83a,0x12c88d,count=4+(n+1)*(157+7*n))
        require(calls==expected,'wrong complete original selection order')
        require(len(set(calls))==len(calls),'original selected a consumed index again')
        stopped=closed and bool(expected)
        destination=0x12c88c if stopped else 0x12c887
        require(em.reg_read(x.UC_X86_REG_EIP)==destination,'wrong final traversal exit')
        remaining=n-len(calls)
        final_counter=remaining if stopped else ((remaining-1)&mask)
        require(em.reg_read(x.UC_X86_REG_ESI)==final_counter,'wrong final counter')
        require(em.reg_read(x.UC_X86_REG_ESP)==sp,'stack not restored after repeated callbacks')
        require(em.reg_read(x.UC_X86_REG_EDI)==65536 and em.reg_read(x.UC_X86_REG_EBP)==initial[5],'preserved registers changed')
        for j in ([] if stopped else expected):records[j][0]=0x7fffffff
        if n:require(bytes(em.mem_read(0x2ba20,12*n))==b''.join(struct.pack('<III',*r) for r in records),'wrong final consumed buffer')
        require(word(sp)==0x12b760 and word(0x2c028)==0x2ba20+12*n,'callback slot or cursor changed')
        groups['empty']+=n==0;groups['full_buffer']+=n==128;groups['wrapping_stack']+=sp<44
        groups['callback_stopped']+=stopped;groups['exhausted']+=not stopped and remaining==0
        groups['range_rejected']+=not stopped and remaining>0
        groups['ties']+=len({fractions[i] for i in expected})<len(expected);groups['negative']+=any(fractions[i]<0 for i in expected)
        total+=len(calls)
    require(all(groups.values()),'missing traversal coverage')
    return dict(cases=count,callbacks=total,groups=groups,callbacks_or_stubs=False,
        scope='Complete authentic repeated traversal with real line callbacks; ordered original-record indices, no duplicates, callback counters/return frames, final buffer and exit checked. Equal-height sectors isolate traversal; earlier diagnostics cover clipping.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-ordered-history';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1TraversalBudget'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Exact production ordered-visitor recursive extraction and induction for arbitrary finite collections and callbacks: original records, no duplicate indices, deterministic equal-length histories, visit bounds and unchanged collection. '
      'Connects history length to the authentic DOS repeat-head counter, including wrapping exhaustion. '
      'Full machine-loop induction, next-callback entry contracts and alignment to the precomputed all-hit aim suffix remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: live source ordered-history induction and original loop-head budget; strict axiom audit.')
if __name__=='__main__':main()

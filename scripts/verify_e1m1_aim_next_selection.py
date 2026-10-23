#!/usr/bin/env python3
"""Authenticate buffer preservation and the next ordered-hit selection."""
import argparse,json,re,subprocess
import verify_e1m1_aim_line_join as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1InterceptMark':['size','selected','other','encoded'],
 'E1M1AimRecordFrame':['frame','records','resumed_records','resumed_frame','registers'],
 'E1M1AimNextSelection':['contains_setup','head_execution','dispatch','after_callback','carried_outcome']}

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimNextSelection\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimNextSelection\nopen Doom Doom.Proofs\n'
    source+='def setupCode : List UInt8 := ['+','.join(hex(b) for b in raw['interceptSetup'])+']\n'
    source+='theorem setup_checked : setupCode=OriginalInterceptSetup.setupCode := by decide\n'
    source+='def scanCode : List UInt8 := ['+','.join(hex(b) for b in raw['interceptMinimum'])+']\n'
    source+='theorem scan_checked : scanCode=OriginalInterceptMinimum.code := by decide\n'
    source+='\n'.join('#print axioms '+n for n in ['setup_checked','scan_checked'])+'\nend Doom.Verification.ExtractedAimNextSelection\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimNextSelection.setup_checked'"
    require(marker in output,'missing aim next-selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimNextSelection.'+n for n in ['setup_checked','scan_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')



def cross_check(raw,count=384):
    """Original callback, mark, loop head, full rescan and real indirect CALL.
    Deliberately uses equal sector heights to isolate the newly connected tail;
    arithmetic/clipping branches have their own earlier diagnostics and proofs.
    """
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    units=[('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340),('aimDistance',0x2b797),('aimFloor',0x2b7a6),('division',0x1d180),('aimCeiling',0x2b7d1),('aimWindow',0x2b800),('aimContinue',0x2b89d),('interceptSetup',0x2c810),('interceptMinimum',0x2c841),('interceptGate',0x2c85e)]
    for name,pc in units:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2c83a);mask=0xffffffff;steps=[]
    pack=lambda v:struct.pack('<I',v&mask)
    def word(a):return struct.unpack('<I',bytes(em.mem_read(a&mask,4)))[0]
    def hook(machine,address,size,data):
        if address in (0x12c887,0x12c88c) or (address==0x12b760 and steps):machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,hook)
    groups=dict(stopped=0,exhausted=0,rejected=0,called=0,tied_next_minimum=0,full_buffer=0,wrapping_stack=0)
    for case in range(count):
        n=[1,2,4,128,8,127][case%6];j=rng.randrange(n);sp=[0x700800,0,4,16,32,0xfffffff0][(case//6)%6]
        counter=0 if case%5==0 else rng.randrange(1,n+1)
        before=[rng.getrandbits(32) for _ in regs];before[0]=before[3]=0x2ba20+12*j;before[4]=sp;before[6]=counter;before[7]=65536
        records=[[rng.choice([65536,65536,65537,0x7fffffff]),rng.randrange(2),rng.getrandbits(32)] for _ in range(n)]
        records[j]=[65536,1,0x600200]
        if case%7==0:
            for i in range(n):
                if i!=j:records[i][0]=0x7fffffff
        lo,hi=(-100,100) if case%11 else (100,100);go=lo<hi
        em.mem_write(0x2ba20,b''.join(struct.pack('<III',*r) for r in records))
        em.mem_write(0x600210,b'\x04');em.mem_write(0x600218,b'\x00\x00')
        cursor=0x2ba20+12*n
        for addr,val in [(0x60022e,0x600300),(0x600232,0x600400),(0x600300,0),(0x600304,128*65536),(0x600400,0),(0x600404,128*65536),(0x2b9b8,65536),(0x2b9a8,32*65536),(0x2c1e4,lo),(0x2c1e8,hi),(sp,0x12c86d),((sp+4)&mask,0x12b760),(0x2c028,cursor)]:em.mem_write(addr,pack(val))
        for reg,val in zip(regs,before):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);steps.clear()
        em.emu_start(0x12b760,0x12c88d,count=158+7*n)
        expected=list(before);expected[0]=int(go);expected[1]=cursor;expected[4]=(sp+4)&mask
        if not go:destination=0x12c88c;groups['stopped']+=1
        else:
            records[j][0]=0x7fffffff;expected[0]=counter;expected[6]=(counter-1)&mask
            if counter==0:destination=0x12c887;groups['exhausted']+=1
            else:
                best=min(r[0] for r in records);chosen=next(i for i,r in enumerate(records) if r[0]==best)
                expected[0]=cursor;expected[2]=best
                if best<0x7fffffff:expected[3]=0x2ba20+12*chosen
                if best>65536:destination=0x12c887;groups['rejected']+=1
                else:
                    destination=0x12b760;expected[0]=expected[3];expected[4]=sp;groups['called']+=1
                    require(word(sp)==0x12c86d,'incorrect real CALL return word')
                    groups['tied_next_minimum']+=sum(r[0]==best for r in records)>1
        require(em.reg_read(x.UC_X86_REG_EIP)==destination,'wrong next boundary')
        require([em.reg_read(r) for r in regs]==expected,'wrong repeat/selection registers')
        require(bytes(em.mem_read(0x2ba20,12*n))==b''.join(struct.pack('<III',*r) for r in records),'record image lost or wrong hit consumed')
        for addr,val in [(0x2c1e4,lo),(0x2c1e8,hi),(0x2c028,cursor),((sp+4)&mask,0x12b760)]:require(word(addr)==(val&mask),'carried state changed')
        require(len(steps)<=157+7*n,'instruction bound exceeded')
        groups['full_buffer']+=n==128;groups['wrapping_stack']+=sp<44
    require(all(groups.values()),'missing next-selection coverage')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,
        scope='Actual open-line callback through parent mark, repeat head, complete rescan and next indirect CALL/exhaustion/range rejection. All registers and complete record buffer checked. Equal sector heights isolate this tail; earlier diagnostics cover clipping branches.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-next-selection';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimNextSelection'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Initial open-line callback memory implies the full consumed-hit buffer image; authentic repeat-loop head and next strict minimum selection reach exhaustion, range rejection or the next indirect callback. '
      'Entry layout, capacity, pointer resolver stability, callback continuation and source/machine arithmetic contracts remain explicit. '
      'No whole-loop induction, actor callback or reachable-state discharge is claimed. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: consumed buffer, preserved traversal state and next ordered selection; strict axiom audit.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Authenticate continuous aiming callback and repeated selection correspondence."""
import argparse,json,re,subprocess
import verify_e1m1_aim_next_selection as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimRepeatProgram':['contains_resume','contains_setup','contains_selection','contains_call','head_execution','dispatch','repeat_selection'],
 'E1M1AimRepeat':['next','execution'],
 'E1M1AimRepeatSource':['correspondence']}
SOURCE_ARGS='s f scene shooter thing path distance i rest lower upper floorSlope ceilingSlope history hit back line frontPtr backPtr h distanceReads floorReads reads clip range eye bottom top selectedPointer selected two backSector pass floorOk ceilingOk returnSafe returnWord markSafe hits resolve j inside bounded image safe pointer listedHit stable cursorSafe cursor maximum targetSafe recordSafe boundsSafe slotSafe slotMark'

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimRepeatSource\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimRepeat\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1AimIteration\nopen E1M1MinimumScan (address)\n'
    source+='def handoffCode : List UInt8 := ['+','.join(hex(b) for b in raw['interceptHandoff'])+']\n'
    source+='theorem handoff_checked : handoffCode=OriginalInterceptSetup.handoffCode := by decide\n'
    source+='def linked : X86Routine.Program := fun pc =>\n  match ExtractedAimLineJoin.linked pc with\n  | some op => some op\n  | none => match OriginalInterceptSetup.bytesProgram ExtractedAimNextSelection.setupCode handoffCode pc with\n    | some op => some op\n    | none => OriginalInterceptMinimum.bytesProgram ExtractedAimNextSelection.scanCode pc\n'
    source+='theorem linked_checked : linked=E1M1AimRepeatProgram.program := by\n  unfold linked E1M1AimRepeatProgram.program OriginalInterceptSetup.program OriginalInterceptMinimum.program\n  rw [ExtractedAimLineJoin.linked_checked,ExtractedAimNextSelection.setup_checked,handoff_checked,ExtractedAimNextSelection.scan_checked]\n  rfl\n'
    text=(ROOT/'Doom/Proofs/E1M1AimRepeatSource.lean').read_text();a=text.index('theorem correspondence ')
    decl=text[a:text.index(' := by',a)].replace('theorem correspondence','theorem correspondence_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1AimRepeatSource.correspondence '+SOURCE_ARGS+'\n'
    source+='\n'.join('#print axioms '+n for n in ['handoff_checked','linked_checked','correspondence_checked'])+'\nend Doom.Verification.ExtractedAimRepeat\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimRepeat.handoff_checked'"
    require(marker in output,'missing aim repeat audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimRepeat.'+n for n in ['handoff_checked','linked_checked','correspondence_checked']]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')



def cross_check(raw,count=384):
    """Original callback, mark, loop head, full rescan and real indirect CALL.
    Includes height-dependent divisions and changed windows at the next boundary.
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
    groups=dict(stopped=0,exhausted=0,rejected=0,called=0,tied_next_minimum=0,full_buffer=0,wrapping_stack=0,floor_clipped=0,ceiling_clipped=0)
    for case in range(count):
        n=[1,2,4,128,8,127][case%6];j=rng.randrange(n);sp=[0x700800,0,4,16,32,0xfffffff0][(case//6)%6]
        counter=0 if case%5==0 else rng.randrange(1,n+1)
        before=[rng.getrandbits(32) for _ in regs];before[0]=before[3]=0x2ba20+12*j;before[4]=sp;before[6]=counter;before[7]=65536
        records=[[rng.choice([65536,65536,65537,0x7fffffff]),rng.randrange(2),rng.getrandbits(32)] for _ in range(n)]
        records[j]=[65536,1,0x600200]
        if case%7==0:
            for i in range(n):
                if i!=j:records[i][0]=0x7fffffff
        ff,bf=[rng.choice([-64,0,16,48])*65536 for _ in range(2)]
        fc,bc=[rng.choice([64,96,128])*65536 for _ in range(2)]
        distance=rng.randrange(1,129)*65536;z=32*65536
        lo,hi=(-64*65536,128*65536) if case%11 else (100,100)
        def div(v):return (abs(v*65536)//distance)*(-1 if v<0 else 1)
        low=lo if ff==bf else max(lo,div(max(ff,bf)-z))
        high=hi if fc==bc else min(hi,div(min(fc,bc)-z))
        go=low<high
        groups['floor_clipped']+=low!=lo;groups['ceiling_clipped']+=high!=hi
        em.mem_write(0x2ba20,b''.join(struct.pack('<III',*r) for r in records))
        em.mem_write(0x600210,b'\x04');em.mem_write(0x600218,b'\x00\x00')
        cursor=0x2ba20+12*n
        for addr,val in [(0x60022e,0x600300),(0x600232,0x600400),(0x600300,ff),(0x600304,fc),(0x600400,bf),(0x600404,bc),(0x2b9b8,distance),(0x2b9a8,z),(0x2c1e4,lo),(0x2c1e8,hi),(sp,0x12c86d),((sp+4)&mask,0x12b760),(0x2c028,cursor)]:em.mem_write(addr,pack(val))
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
        for addr,val in [(0x2c1e4,low),(0x2c1e8,high),(0x2c028,cursor),((sp+4)&mask,0x12b760)]:require(word(addr)==(val&mask),'carried state changed')
        require(len(steps)<=157+7*n,'instruction bound exceeded')
        groups['full_buffer']+=n==128;groups['wrapping_stack']+=sp<44
    require(all(groups.values()),'missing next-selection coverage')
    return dict(cases=count,groups=groups,callbacks_or_stubs=False,
        scope='Original callback with height-dependent clipping through mark, repeat, complete rescan and next indirect CALL or exit. All registers, buffer words, bounds, cursor and callback slot checked.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-repeat';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimRepeatSource'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='One continuous decoded program executes the open-line callback, parent stop/mark decision and next ordered selection. The next boundary carries the clipped bounds; the Lean continuation carries the matching window and portal history. '
      'Initial representations, memory separation, source divisions and selected-hit alignment remain explicit. '
      'Whole repeated-loop induction, actor targeting and reachable-state discharge remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: continuous callback-to-next-selection with carried bounds and live source continuation; strict axiom audit.')
if __name__=='__main__':main()

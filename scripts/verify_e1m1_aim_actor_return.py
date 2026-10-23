#!/usr/bin/env python3
"""Authenticate successful actor return and aligned traversal stop with original DOS bytes."""
import argparse,json,re,subprocess
import verify_e1m1_aim_actor_select as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimActorReturn': ['contains_repeat', 'contains_guard', 'clipped_frame', 'selected_fields', 'selected_frame', 'saved_slot', 'returned_fields', 'registers', 'continuation', 'frame', 'execution'], 'E1M1AimActorStop': ['stores_apart', 'records', 'safe_transfer', 'execution']}
EXEC_ARGS=previous.SELECT_ARGS+' saveSafe returnWord'
STOP_ARGS=previous.CYCLE_ARGS.replace('above','bottomAdmitted saveSafe')
CONTRACTS=[('E1M1AimActorReturn','execution','return_checked',EXEC_ARGS),
 ('E1M1AimActorStop','execution','stop_checked',STOP_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.E1M1AimActorSelect.program',decl)
    for word in ['result','returned','Safe']:
        owner='E1M1AimWall' if word=='Safe' and module=='E1M1AimActorStop' else 'E1M1AimActorReturn'
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    decl=decl.replace('(selected s)','(Doom.Proofs.E1M1AimActorReturn.selected s)')
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorStop\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorReturn\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  rw [linked_checked]\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorReturn\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorReturn.linked_checked'"
    require(marker in output,'missing actor return audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorReturn.linked_checked']
    names+=['Doom.Verification.ExtractedAimActorReturn.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(spec,raw,count=384):
    """Execute original bytes independently; finite checks supplement the proofs."""
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x50000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name in ['aimGuard','aimStop','aimActorGuard','aimActorTop','aimActorBottom','aimContinue','aimActorSelect','division','interceptGate','interceptSetup','interceptMinimum']:
        em.mem_write(0x100000+int(spec['units'][name]['code_offset'],16),raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b881);mask=0xffffffff;writes=[];steps=[];snapshots={}
    signed=lambda v:(v&mask) if (v&mask)<2**31 else (v&mask)-2**32
    pack=lambda v:struct.pack('<I',v&mask)
    def divide(num,den):
        guard=(signed(abs(num))>>14)<signed(abs(den))
        if guard:
            q=(abs(num*65536)//abs(den))*(-1 if (num<0)!=(den<0) else 1)
            require(-2**31<=q<2**31,'invalid generated division')
        else:q=-2**31 if (num<0)!=(den<0) else 2**31-1
        return q,guard,(num*65536-q*den)&mask if guard else (mask if den<0 else 0)
    def cmpflags(a,b):
        a&=mask;b&=mask;d=(a-b)&mask
        return int(a<b)|(int((d&255).bit_count()%2==0)<<2)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    def on_code(machine,address,size,data):
        if address in [0x12b881,0x12b89d,0x12b8a9,0x12b8d2,0x12c86d,0x12c83a]:
            snapshots[address]=([machine.reg_read(r) for r in regs],machine.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5,len(writes),len(steps))
        if address in [0x12c88c,0x12c887] or (address==0x12b760 and steps):machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,on_code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4]&mask)))
    groups=dict(both_normal=0,both_saturated=0,mixed_division=0,bottom_below=0,bottom_equal=0,bottom_above=0,
                top_equal=0,top_above=0,negative_distance=0,wrapped_bottom=0,wrapping_stack=0,
                next_callback=0,exhausted=0,beyond_range=0,tied_minimum=0,capacity_128=0,
                top_clipped=0,top_retained=0,bottom_clipped=0,bottom_retained=0,negative_odd_midpoint=0,wrapped_midpoint=0)
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        actor=0x600201+case%4;who=0x600301;record=0x2ba20
        length=[1,2,4,8,128][case%5];cursor=record+12*length
        before=[rng.getrandbits(32) for _ in regs];before[0]=before[3]=record;before[4]=sp
        before[6]=length-1;before[7]=65536
        targetZ,height,eye=[signed(rng.getrandbits(32)) for _ in range(3)]
        frac=8192
        if case%4==0:distance=8
        elif case%4==1:distance=0x40000000
        elif case%4==2:
            distance=524288;eye=signed(targetZ-65536);height=1500000000
        else:distance=-0x40000000
        dist=signed((distance*frac)>>16)
        topNum=signed(targetZ+height-eye);bottomNum=signed(targetZ-eye)
        topSlope,topNormal,topRemainder=divide(topNum,dist)
        bottomSlope,bottomNormal,bottomRemainder=divide(bottomNum,dist)
        lower=topSlope if case%2==0 else max(-2**31,topSlope-1-rng.randrange(100))
        upper=bottomSlope if case%3==0 else signed(rng.getrandbits(32))
        above=upper<bottomSlope
        far=case%7==0
        fractions=[frac]+[70000+rng.randrange(10000) if far else 8192+rng.randrange(50000) for _ in range(length-1)]
        if length>2 and case%2==0:fractions[1]=fractions[2]=70000 if far else 8192
        image=b''.join(pack(v)+pack(i%2 if i else 0)+pack(actor+128*i) for i,v in enumerate(fractions))
        em.mem_write(record,image);em.mem_write(actor+104,bytes([rng.randrange(256)|4]))
        protected=[(actor+20,targetZ),(actor+68,height),(0x2b9ac,who),(0x2b9b8,distance),
                   (0x2b9a8,eye),(0x2c1e4,lower),(0x2c1e8,upper),(sp,0x12c86d),((sp+4)&mask,0x12b760)]
        for addr,value in protected+[(0x2c028,cursor)]:em.mem_write(addr,pack(value))
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear();snapshots.clear()
        em.emu_start(0x12b760,0x12c88d,count=116+7*length)
        require(0x12b881 in snapshots,'top did not admit bottom calculation')
        topRegs,topFlags,topWrites,topSteps=snapshots[0x12b881]
        expected=list(before);expected[0]=expected[6]=expected[7]=topSlope&mask
        expected[1]=actor;expected[2]=topRemainder;expected[3]=dist&mask
        expected[4]=(sp-24)&mask;expected[5]=eye&mask
        require(topRegs==expected and topFlags==cmpflags(topSlope,lower),'top boundary mismatch')
        require(topWrites==10 and topSteps<=56,'top write/count mismatch')
        gate=0x12b89d if above else 0x12b8a9
        require(gate in snapshots,'missing exact bottom decision')
        bottomRegs,bottomFlags,bottomWrites,bottomSteps=snapshots[gate]
        expected[0]=bottomSlope&mask;expected[2]=bottomRemainder;expected[3]=upper&mask
        require(bottomRegs==expected and bottomFlags==cmpflags(bottomSlope,upper),'bottom gate registers/flags mismatch')
        require(bottomWrites==14 and bottomSteps<=89 and bottomSteps-topSteps<=33,'second division write/count mismatch')
        expectedWrites=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        expectedWrites += [((sp-off)&mask,4,value&mask) for off,value in
                          [(28,0x12b869),(32,dist),(36,actor),(40,who),
                           (28,0x12b893),(32,dist),(36,actor),(40,topSlope)]]
        if above:
            expected=list(before);expected[0]=1;expected[1]=cursor;expected[4]=(sp+4)&mask
            parentRegs,parentFlags,parentWrites,parentSteps=snapshots[0x12c83a]
            require(parentRegs==expected and parentFlags==0,'restored parent mismatch')
            require(parentSteps-bottomSteps==13 and parentSteps<=102 and parentWrites==15,'parent count mismatch')
            expectedWrites.append((record,4,0x7fffffff))
            expected[6]=(length-2)&mask
            if length==1:
                expected[0]=0;final_pc=0x12c887;final_flags=0x44;groups['exhausted']+=1
            else:
                best=min(range(1,length),key=lambda i:fractions[i]);value=fractions[best]
                expected[2]=value;expected[3]=record+12*best
                expectedWrites.append((0x2c028,4,cursor))
                final_flags=cmpflags(value,65536)
                if value>65536:
                    expected[0]=cursor;final_pc=0x12c887;groups['beyond_range']+=1
                else:
                    expected[0]=record+12*best;expected[4]=sp;final_pc=0x12b760;groups['next_callback']+=1
                    expectedWrites.append((sp,4,0x12c86d))
                groups['tied_minimum']+=fractions.count(value)>1
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==final_flags,'scan flags mismatch')
            require(len(steps)<=115+7*length,'bottom cycle bound mismatch')
        else:
            clippedTop=min(topSlope,upper);clippedBottom=max(bottomSlope,lower)
            total=signed(clippedTop+clippedBottom)
            center=(abs(total)//2)*(-1 if total<0 else 1)
            expected[0]=center&mask;expected[2]=mask if total<0 else 0;expected[7]=clippedTop&mask
            selectedRegs,_,selectedWrites,selectedSteps=snapshots[0x12b8d2]
            require(selectedRegs==expected and selectedWrites==16,'selection registers or writes mismatch')
            require(selectedSteps<=103 and selectedSteps-bottomSteps<=14,'selection bound mismatch')
            returnedRegs,returnedFlags,returnedWrites,returnedSteps=snapshots[0x12c86d]
            expected=list(before);expected[0]=0;expected[4]=(sp+4)&mask
            require(returnedRegs==expected and returnedFlags==0x44,'six-register false return mismatch')
            require(returnedWrites==16 and returnedSteps-selectedSteps==8,'false return wrote memory or wrong step count')
            expected[1]=cursor;final_pc=0x12c88c
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==0x44,'parent false-return flags mismatch')
            require(len(steps)-returnedSteps==4 and len(steps)<=115,'parent stop step bound mismatch')
            expectedWrites += [(0x2b9f8,4,actor),(0x2b9b4,4,center&mask)]
            require(bytes(em.mem_read(0x2b9f8,4))==pack(actor),'selected target store mismatch')
            require(bytes(em.mem_read(0x2b9b4,4))==pack(center),'selected slope store mismatch')
            groups['top_clipped']+=topSlope>upper;groups['top_retained']+=topSlope<=upper
            groups['bottom_clipped']+=bottomSlope<lower;groups['bottom_retained']+=bottomSlope>=lower
            groups['negative_odd_midpoint']+=total<0 and total%2!=0
            groups['wrapped_midpoint']+=total!=clippedTop+clippedBottom
        require(em.reg_read(x.UC_X86_REG_EIP)==final_pc,'wrong final PC')
        require([em.reg_read(r) for r in regs]==expected,'final registers mismatch')
        require(writes==expectedWrites,'ordered callback/division/scan/selection writes mismatch')
        require(steps.count(0x11d180)==2,'did not execute both real divisions')
        require(bytes(em.mem_read(record,len(image)))==(pack(0x7fffffff)+image[4:] if above else image),'record mark mismatch')
        for addr,value in protected:require(bytes(em.mem_read(addr,4))==pack(value),'protected word changed')
        groups['both_normal']+=topNormal and bottomNormal;groups['both_saturated']+=not topNormal and not bottomNormal
        groups['mixed_division']+=topNormal!=bottomNormal;groups['bottom_below']+=bottomSlope<upper
        groups['bottom_equal']+=bottomSlope==upper;groups['bottom_above']+=above
        groups['top_equal']+=topSlope==lower;groups['top_above']+=topSlope>lower
        groups['negative_distance']+=dist<0;groups['wrapped_bottom']+=bottomNum!=targetZ-eye;groups['wrapping_stack']+=sp<40;groups['capacity_128']+=length==128
    require(all(groups.values()),'missing branch coverage: '+str(groups))
    return dict(cases=count,groups=groups,all_registers_checked=True,
                modeled_compare_return_parent_and_scan_flags_checked=True,selection_intermediate_flags_unmodeled=True,
                ordered_callback_division_scan_selection_writes_checked=True,callbacks_or_stubs=False,
                scope='Actual eligible callback through both real divisions. Bottom rejections execute the return, parent mark and complete next scan; admitted actors execute clipping, midpoint and stores through the real false-return epilogue and parent stop. All saved registers are restored, selected stores survive, and the selected intercept remains unmarked. The traversal function epilogue is not executed.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-return';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorStop'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Actual eligible callback through both divisions, clipping, target/slope stores, false return and parent stop. '
      'Six saved registers and stack are restored; the full intercept buffer remains unmarked on this branch. '
      'Actual selected-index/history alignment joins the machine result to the canonical source suffix and exact target/window/path result. '
      'Representation, arithmetic success, admission, source alignment and memory separation remain explicit. '
      'The traversal epilogue, actor catalogs, mixed-loop composition and whole aiming remain open. No runtime or semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(spec,raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: successful actor return and aligned traversal stop; strict axiom audit.')
if __name__=='__main__':main()

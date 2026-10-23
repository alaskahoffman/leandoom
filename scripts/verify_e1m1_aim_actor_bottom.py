#!/usr/bin/env python3
"""Authenticate both actor slopes and bottom rejection through the real parent return."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_e1m1_aim_actor_reject as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'OriginalAimActorBottom':['decoded','call_execution','gate_execution','operands'],
 'E1M1AimActorBottom':['contains_bottom','contains_prior','contains_division','call_fields','returned','frame','division_edi','division_success','execution'],
 'E1M1AimActorBottomEntry':['contains_top','body_safe','frame','execution','source_reject'],
 'E1M1AimActorBottomReject':['contains_repeat','contains_window','stack','body_frame','saved_slot','returned_fields','registers','read_frame','frame','continuation','execution']}
EXEC_ARGS='s f hit pointer who range targetZ targetHeight shootZ lower upper topSlope bottomSlope record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter different shootable topSafe safe r z0 ht eye0 low high topOk admitted bottomOk'
REJECT_ARGS='s f scene shooterId thing path range lower upper topSlope bottomSlope log i rest hit pointer who record selected isThing tagSafe pointerSafe shooterSafe flagsSafe shooter identity flags different shootable topSafe safe r z0 ht eye0 bound high topOk admitted bottomOk above returnWord'
CONTRACTS=[('E1M1AimActorBottomEntry','execution','execution_checked',EXEC_ARGS),
 ('E1M1AimActorBottomReject','execution','rejection_checked',REJECT_ARGS)]

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-actor-bottom.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate actor bottom range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

HEADER='''
set_option backward.isDefEq.respectTransparency false
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimIteration
open E1M1AimHistoryCycle (Frame)
open E1M1AimWall (Safe)
open E1M1MinimumScan (address)
'''

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    prog='OriginalAimActorBottom' if module=='OriginalAimActorBottom' else 'E1M1AimActorBottom'
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.'+prog+'.program',decl)
    for word in ['ReadSafe','result','input','call','divided','bottom','returned']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+module+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorBottomReject\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorBottom\n'+HEADER
    source+='def code : List UInt8 := ['+','.join(hex(b) for b in raw['aimActorBottom'])+']\n'
    source+='theorem code_checked : code=OriginalAimActorBottom.code := by decide\n'
    source+='def linked : X86Routine.Program := fun pc => match OriginalAimActorBottom.bytesProgram code pc with | some op => some op | none => E1M1AimActorReject.program pc\n'
    source+='theorem linked_checked : linked=E1M1AimActorBottom.program := congrArg (fun bytes : List UInt8 => fun pc => match OriginalAimActorBottom.bytesProgram bytes pc with | some op => some op | none => E1M1AimActorReject.program pc) code_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorBottom.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  rw [linked_checked]\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms code_checked\n#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorBottom\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorBottom.code_checked'"
    require(marker in output,'missing actor bottom audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorBottom.code_checked','Doom.Verification.ExtractedAimActorBottom.linked_checked']
    names+=['Doom.Verification.ExtractedAimActorBottom.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    for name in ['aimGuard','aimActorGuard','aimActorTop','aimActorBottom','aimContinue','division','interceptGate','interceptSetup']:
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
        if address in [0x12b881,0x12b89d,0x12b8a9,0x12c83a]:
            snapshots[address]=([machine.reg_read(r) for r in regs],machine.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5,len(writes),len(steps))
        if address in [0x12b8a9,0x12c83a]:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,on_code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4]&mask)))
    groups=dict(both_normal=0,both_saturated=0,mixed_division=0,bottom_below=0,bottom_equal=0,bottom_above=0,
                top_equal=0,top_above=0,negative_distance=0,wrapped_bottom=0,wrapping_stack=0)
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        actor=0x600201+case%4;who=0x600301;record=0x2ba20;cursor=record+24
        before=[rng.getrandbits(32) for _ in regs];before[0]=before[3]=record;before[4]=sp
        before[6]=1;before[7]=65536
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
        image=pack(frac)+pack(0)+pack(actor)+pack(40000)+pack(1)+pack(0x600381)
        em.mem_write(record,image);em.mem_write(actor+104,bytes([rng.randrange(256)|4]))
        protected=[(actor+20,targetZ),(actor+68,height),(0x2b9ac,who),(0x2b9b8,distance),
                   (0x2b9a8,eye),(0x2c1e4,lower),(0x2c1e8,upper),(sp,0x12c86d),((sp+4)&mask,0x12b760)]
        for addr,value in protected+[(0x2c028,cursor)]:em.mem_write(addr,pack(value))
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear();snapshots.clear()
        em.emu_start(0x12b760,0x12b8aa,count=103)
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
        require(em.reg_read(x.UC_X86_REG_EIP)==(0x12c83a if above else 0x12b8a9),'wrong final PC')
        require(writes==expectedWrites,'ordered first/second division/parent writes mismatch')
        require(steps.count(0x11d180)==2,'did not execute both real divisions')
        require(bytes(em.mem_read(record,len(image)))==(pack(0x7fffffff)+image[4:] if above else image),'record mark mismatch')
        for addr,value in protected:require(bytes(em.mem_read(addr,4))==pack(value),'protected word changed')
        groups['both_normal']+=topNormal and bottomNormal;groups['both_saturated']+=not topNormal and not bottomNormal
        groups['mixed_division']+=topNormal!=bottomNormal;groups['bottom_below']+=bottomSlope<upper
        groups['bottom_equal']+=bottomSlope==upper;groups['bottom_above']+=above
        groups['top_equal']+=topSlope==lower;groups['top_above']+=topSlope>lower
        groups['negative_distance']+=dist<0;groups['wrapped_bottom']+=bottomNum!=targetZ-eye;groups['wrapping_stack']+=sp<40
    require(all(groups.values()),'missing bottom slope/rejection coverage')
    return dict(cases=count,groups=groups,all_registers_and_modeled_flags_checked=True,
                ordered_two_division_and_parent_writes_checked=True,callbacks_or_stubs=False,
                scope='Actual eligible callback through both divisions and bottom decision; strict rejections execute original epilogue and parent mark. Admitted actors stop before clipping/selection; no next scan is executed.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-bottom';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorBottomReject'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Authenticated eligible callback through both slope divisions and the signed upper-window test. '
      'Equality remains admitted. Strict bottom rejection joins the production source suffix to the actual restored return and parent mark. '
      'Representation, admitted top, arithmetic success and read-separation premises remain explicit. '
      'The bottom-rejection next scan, clipping/selection, actor catalogs and whole aiming remain open. No runtime or semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(spec,raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actor bottom slope and strict rejection through restored return and parent; strict axiom audit.')
if __name__=='__main__':main()

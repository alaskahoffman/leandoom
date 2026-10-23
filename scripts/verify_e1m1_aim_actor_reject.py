#!/usr/bin/env python3
"""Authenticate the eligible actor top rejection through the real next traversal boundary."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_e1m1_aim_actor_top as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'OriginalAimActorReject':['decoded','execution'],
 'E1M1AimActorReject':['contains_return','contains_top','contains_repeat','stack','top_frame','saved_slot','returned_fields','registers','read_frame','frame','continuation','execution'],
 'E1M1AimActorRejectCycle':['read_safe','records','scan','carried','execution']}
EXEC_ARGS=previous.REJECT_ARGS+' returnWord'
SCAN_ARGS='s f initial work seen visits resolve target sp fraction j history selection layout bounded stable'
CYCLE_ARGS='s f scene shooter thing path original distance lower upper slope log work seen visits resolve target sp who fraction j history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags different shootable safe z0 ht ok below'
CONTRACTS=[('E1M1AimActorReject','execution','execution_checked',EXEC_ARGS),
 ('E1M1AimActorRejectCycle','scan','scan_checked',SCAN_ARGS),
 ('E1M1AimActorRejectCycle','execution','cycle_checked',CYCLE_ARGS)]

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-actor-reject.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate actor top range')
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
    prog='OriginalAimActorReject' if module=='OriginalAimActorReject' else 'E1M1AimActorReject'
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.'+prog+'.program',decl)
    for word in ['top','result','returned']:
        decl=decl.replace('('+word+' s)','(Doom.Proofs.E1M1AimActorReject.'+word+' s)')
    decl=re.sub(r'(?<![.\w])ReadSafe\b','Doom.Proofs.E1M1AimActorReject.ReadSafe',decl)
    decl=re.sub(r'(?<![.\w])Next\b','Doom.Proofs.E1M1AimActorRejectCycle.Next',decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorRejectCycle\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorReject\n'+HEADER
    source+='def code : List UInt8 := ['+','.join(hex(b) for b in raw['aimActorReject'])+']\n'
    source+='theorem code_checked : code=OriginalAimActorReject.code := by decide\n'
    source+='def linked : X86Routine.Program := fun pc => match OriginalAimActorReject.bytesProgram code pc with | some op => some op | none => E1M1AimActorTop.program pc\n'
    source+='theorem linked_checked : linked=E1M1AimActorReject.program := congrArg (fun bytes : List UInt8 => fun pc => match OriginalAimActorReject.bytesProgram bytes pc with | some op => some op | none => E1M1AimActorTop.program pc) code_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorReject.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  rw [linked_checked]\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms code_checked\n#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorReject\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorReject.code_checked'"
    require(marker in output,'missing actor top audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorReject.code_checked','Doom.Verification.ExtractedAimActorReject.linked_checked']
    names+=['Doom.Verification.ExtractedAimActorReject.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(spec,raw,count=384):
    """Finite independent x86 checks; the Lean theorems provide universal claims."""
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x50000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name in ['aimGuard','aimActorGuard','aimActorTop','aimActorReject','division','interceptSetup','interceptMinimum','interceptGate']:
        em.mem_write(0x100000+int(spec['units'][name]['code_offset'],16),raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b875);mask=0xffffffff;writes=[];steps=[];snapshots={}
    signed=lambda v:(v&mask) if (v&mask)<2**31 else (v&mask)-2**32
    pack=lambda v:struct.pack('<I',v&mask)
    def cmpflags(a,b):
        a&=mask;b&=mask;d=(a-b)&mask
        return int(a<b)|(int((d&255).bit_count()%2==0)<<2)|(int(d==0)<<6)|((d>>31)<<7)|(int(bool((a^b)&(a^d)&0x80000000))<<11)
    def on_code(machine,address,size,data):
        if address in [0x12b875,0x12c83a]:
            snapshots[address]=([machine.reg_read(r) for r in regs],machine.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5,len(writes),len(steps))
        if (address==0x12b760 and steps) or address==0x12c887:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,on_code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4]&mask)))
    groups=dict(normal=0,saturated=0,next_callback=0,exhausted=0,beyond_range=0,tied_minimum=0,
                negative_distance=0,negative_slope=0,wrapping_stack=0,capacity_128=0)
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        actor=0x600201+case%4;who=0x600301;record=0x2ba20
        length=[1,2,4,8,128][case%5];cursor=record+12*length
        before=[rng.getrandbits(32) for _ in regs]
        before[0]=before[3]=record;before[4]=sp;before[6]=length-1;before[7]=65536
        targetZ,height,eye=[signed(rng.getrandbits(32)) for _ in range(3)]
        frac=8192;distance=8 if case%4==0 else (-0x40000000 if case%3==0 else 0x40000000)
        dist=signed((distance*frac)>>16)
        if case%4==0:eye=signed(targetZ+height+131072)
        num=signed(targetZ+height-eye)
        guard=(signed(abs(num))>>14)<signed(abs(dist))
        if guard:
            quotient=(abs(num*65536)//abs(dist))*(-1 if (num<0)!=(dist<0) else 1)
            require(-2**31<=quotient<2**31,'invalid generated division')
        else:quotient=-2**31 if (num<0)!=(dist<0) else 2**31-1
        require(quotient<2**31-1,'generated unrejectable maximum slope')
        lower=quotient+1+rng.randrange(100);upper=signed(rng.getrandbits(32))
        far=case%3==0
        fractions=[frac]+[70000+rng.randrange(10000) if far else 8192+rng.randrange(50000) for _ in range(length-1)]
        if length>2 and case%2==0:fractions[1]=fractions[2]=70000 if far else 8192
        image=b''.join(pack(v)+pack(i%2 if i else 0)+pack(actor+128*i) for i,v in enumerate(fractions))
        em.mem_write(record,image);em.mem_write(actor+104,bytes([rng.randrange(256)|4]))
        protected=[(actor+20,targetZ),(actor+68,height),(0x2b9ac,who),(0x2b9b8,distance),
                   (0x2b9a8,eye),(0x2c1e4,lower),(0x2c1e8,upper),((sp+4)&mask,0x12b760)]
        for addr,value in protected+[(sp,0x12c86d),(0x2c028,cursor)]:em.mem_write(addr,pack(value))
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear();snapshots.clear()
        em.emu_start(0x12b760,0x12c888,count=83+7*length)
        require(0x12b875 in snapshots and 0x12c83a in snapshots,'missing rejection/parent boundary')
        top_regs,top_flags,top_writes,top_steps=snapshots[0x12b875]
        expected=list(before);expected[0]=expected[6]=expected[7]=quotient&mask
        expected[1]=actor;expected[2]=(num*65536-quotient*dist)&mask if guard else (mask if dist<0 else 0)
        expected[3]=dist&mask;expected[4]=(sp-24)&mask;expected[5]=eye&mask
        require(top_regs==expected and top_flags==cmpflags(quotient,lower),'top decision mismatch')
        require(top_steps<=56 and top_writes==10,'top execution bound/write count mismatch')
        expected=list(before);expected[0]=1;expected[1]=cursor;expected[4]=(sp+4)&mask
        parent_regs,parent_flags,parent_writes,parent_steps=snapshots[0x12c83a]
        require(parent_regs==expected and parent_flags==0,'restoration/parent registers or flags mismatch')
        require(parent_steps<=69 and parent_steps-top_steps==13 and parent_writes==11,'return/parent bound mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        expected_writes += [((sp-off)&mask,4,value&mask) for off,value in [(28,0x12b869),(32,dist),(36,actor),(40,who)]]
        expected_writes += [(record,4,0x7fffffff)]
        expected[6]=(length-2)&mask
        if length==1:
            expected[0]=0;final_pc=0x12c887;final_flags=0x44;groups['exhausted']+=1
        else:
            best=min(range(1,length),key=lambda i:fractions[i]);value=fractions[best]
            expected[2]=value;expected[3]=record+12*best
            expected_writes += [(0x2c028,4,cursor)]
            final_flags=cmpflags(value,65536)
            if value>65536:
                expected[0]=cursor;final_pc=0x12c887;groups['beyond_range']+=1
            else:
                expected[0]=record+12*best;expected[4]=sp;final_pc=0x12b760;groups['next_callback']+=1
                expected_writes += [(sp,4,0x12c86d)]
            groups['tied_minimum']+=fractions.count(value)>1
        require(em.reg_read(x.UC_X86_REG_EIP)==final_pc,'wrong final boundary')
        require([em.reg_read(r) for r in regs]==expected,'final scan registers mismatch')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==final_flags,'final scan flags mismatch')
        require(writes==expected_writes,'ordered callback/parent/scan writes mismatch')
        require(bytes(em.mem_read(record,len(image)))==pack(0x7fffffff)+image[4:],'wrong consumed record image')
        require(len(steps)<=82+7*length,'full cycle instruction bound mismatch')
        require(0x11d180 in steps and (0x11d1c0 if guard else 0x11d1b0) in steps,'missing real division RET')
        for addr,value in protected:require(bytes(em.mem_read(addr,4))==pack(value),'protected word changed')
        groups['normal']+=guard;groups['saturated']+=not guard;groups['negative_distance']+=dist<0
        groups['negative_slope']+=quotient<0;groups['wrapping_stack']+=sp<40;groups['capacity_128']+=length==128
    require(all(groups.values()),'missing rejection/scan coverage')
    return dict(cases=count,groups=groups,all_registers_and_modeled_flags_checked=True,
                ordered_stack_parent_scan_writes_checked=True,callbacks_or_stubs=False,
                scope='Actual callback entry through real division, strict top rejection, restored return, parent mark, full next minimum scan and callback/exit boundary; no execution of the next callback body.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-reject';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorRejectCycle'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Authenticated eligible actor callback through top-slope rejection, six-register return, parent marking, full next scan and actual next callback or exit. '
      'The joined cycle derives consumed history, unchanged aim bounds, source continuation and the preserved traversal invariant. '
      'Source division success, actor representation, source path alignment and initial traversal/layout premises remain explicit. '
      'Actor catalogs, other actor branches, full mixed loop and whole aiming remain open. No runtime or instruction-semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(spec,raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: eligible actor top rejection through return, parent and next scan; strict axiom audit.')
if __name__=='__main__':main()

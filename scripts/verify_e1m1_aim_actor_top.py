#!/usr/bin/env python3
"""Authenticate eligible actor top slope and first vertical rejection decision."""
import argparse,json,re,subprocess
import verify_original_inline_thrust as extraction
import verify_e1m1_aim_actor_cycle as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'OriginalAimActorTop':['decoded','call_execution','gate_execution','operands'],
 'E1M1AimActorTop':['contains_top','contains_skip','contains_division','call_fields','returned','frame','division_success','execution'],
 'E1M1AimActorTopEntry':['prologue_safe','entry','reached_fields','inputs','lower_safe','execution','source_reject','reject']}
EXEC_ARGS='s f hit pointer who range targetZ targetHeight shootZ lower slope record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter different shootable safe r z0 ht eye0 bound ok'
REJECT_ARGS='s f scene shooterId thing path range lower upper slope log i rest hit pointer who record selected isThing tagSafe pointerSafe shooterSafe flagsSafe shooter identity flags different shootable safe r z0 ht eye0 bound ok below'
CONTRACTS=[('E1M1AimActorTopEntry','execution','execution_checked',EXEC_ARGS),
 ('E1M1AimActorTopEntry','reject','reject_checked',REJECT_ARGS)]

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-actor-top.json').read_text())
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
    prog='OriginalAimActorTop' if module=='OriginalAimActorTop' else 'E1M1AimActorTop'
    decl=re.sub(r'\bprogram\b','Doom.Proofs.'+prog+'.program',decl)
    for word in ['ReadSafe','result','entered','call','divided']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+module+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorTopEntry\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorTop\n'+HEADER
    source+='def code : List UInt8 := ['+','.join(hex(b) for b in raw['aimActorTop'])+']\n'
    source+='theorem code_checked : code=OriginalAimActorTop.code := by decide\n'
    source+='def linked : X86Routine.Program := fun pc => match OriginalAimActorTop.bytesProgram code pc with | some op => some op | none => E1M1AimActorSkip.program pc\n'
    source+='theorem linked_checked : linked=E1M1AimActorTop.program := congrArg (fun bytes : List UInt8 => fun pc => match OriginalAimActorTop.bytesProgram bytes pc with | some op => some op | none => E1M1AimActorSkip.program pc) code_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorTop.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  rw [linked_checked]\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms code_checked\n#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorTop\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorTop.code_checked'"
    require(marker in output,'missing actor top audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorTop.code_checked','Doom.Verification.ExtractedAimActorTop.linked_checked']
    names+=['Doom.Verification.ExtractedAimActorTop.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,count=384):
    import random,struct,unicorn as u
    from unicorn import x86_const as x
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name,pc in [('aimGuard',0x2b760),('aimActorGuard',0x2b81a),('aimActorTop',0x2b843),('division',0x1d180)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b843);mask=0xffffffff;writes=[];steps=[]
    signed=lambda v:(v&mask) if (v&mask)<2**31 else (v&mask)-2**32
    pack=lambda v:struct.pack('<I',v&mask)
    def on_code(machine,address,size,data):
        if address in [0x12b875,0x12b881]:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,on_code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4]&mask)))
    groups=dict(normal=0,saturated=0,below=0,equal=0,above=0,negative_distance=0,negative_slope=0,wrapped_height_sum=0,wrapped_subtraction=0,wrapping_stack=0)
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        actor=0x600201+(case%4);who=0x600301;record=0x600100
        before=[rng.getrandbits(32) for _ in regs];before[0]=record;before[4]=sp
        targetZ,height,eye=[signed(rng.getrandbits(32)) for _ in range(3)]
        distance=signed(rng.getrandbits(32));frac=[65536,-65536,signed(rng.getrandbits(32))][case%3]
        if case%4==0:distance=1;frac=65536
        dist=signed((distance*frac)>>16);top=signed(targetZ+height);num=signed(top-eye)
        guard=(signed(abs(num))>>14)<signed(abs(dist))
        if guard:
            require(dist!=0,'invalid generated normal denominator')
            quotient=(abs(num*65536)//abs(dist))*(-1 if (num<0)!=(dist<0) else 1)
            require(-2**31<=quotient<2**31,'invalid generated IDIV overflow')
        else:quotient=-2**31 if (num<0)!=(dist<0) else 2**31-1
        lower=quotient if case%3==0 else signed(rng.getrandbits(32))
        upper=signed(rng.getrandbits(32));tag=bytes([rng.randrange(256)|4])
        image=pack(frac)+pack(0)+pack(actor)
        em.mem_write(record,image);em.mem_write(actor+104,tag)
        for addr,value in [(actor+20,targetZ),(actor+68,height),(0x2b9ac,who),(0x2b9b8,distance),(0x2b9a8,eye),(0x2c1e4,lower),(0x2c1e8,upper),(sp,0x12c86d)]:em.mem_write(addr,pack(value))
        for reg,value in zip(regs,before):em.reg_write(reg,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear()
        em.emu_start(0x12b760,0x12b881,count=57)
        require(em.reg_read(x.UC_X86_REG_EIP)==(0x12b875 if quotient<lower else 0x12b881),'actor top signed branch mismatch')
        require(len(steps)<=56,'actor top instruction bound mismatch')
        expected=list(before);expected[0]=expected[6]=expected[7]=quotient&mask
        expected[1]=actor;expected[2]=(num*65536-quotient*dist)&mask if guard else (mask if dist<0 else 0)
        expected[3]=dist&mask;expected[4]=(sp-24)&mask;expected[5]=eye&mask
        require([em.reg_read(r) for r in regs]==expected,'actor top register mismatch')
        a,b=quotient&mask,lower&mask;delta=(a-b)&mask
        cmp_flags=(int(a<b)| (int((delta&255).bit_count()%2==0)<<2)| (int(delta==0)<<6)| ((delta>>31)<<7)| (int(bool((a^b)&(a^delta)&0x80000000))<<11))
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==cmp_flags,'actor top comparison flags mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        expected_writes += [((sp-off)&mask,4,value&mask) for off,value in [(28,0x12b869),(32,dist),(36,actor),(40,who)]]
        require(writes==expected_writes,'actor top ordered stack writes mismatch')
        require(0x11d180 in steps and (0x11d1c0 if guard else 0x11d1b0) in steps,'missing real division RET')
        for addr,value in [(actor+20,targetZ),(actor+68,height),(0x2b9ac,who),(0x2b9b8,distance),(0x2b9a8,eye),(0x2c1e4,lower),(0x2c1e8,upper),(sp,0x12c86d)]:
            require(bytes(em.mem_read(addr,4))==pack(value),'protected actor/global word changed')
        require(bytes(em.mem_read(record,12))==image,'intercept changed before rejection return')
        groups['normal']+=guard;groups['saturated']+=not guard
        groups['below']+=quotient<lower;groups['equal']+=quotient==lower;groups['above']+=quotient>lower
        groups['negative_distance']+=dist<0;groups['negative_slope']+=quotient<0
        groups['wrapped_height_sum']+=top!=targetZ+height;groups['wrapped_subtraction']+=num!=top-eye;groups['wrapping_stack']+=sp<40
    require(all(groups.values()),'missing actor top coverage')
    return dict(cases=count,groups=groups,all_registers_and_modeled_flags_checked=True,ordered_stack_writes_checked=True,
      callbacks_or_stubs=False,scope='Actual eligible callback through top-slope division RET and signed rejection decision only; no rejection epilogue, bottom slope or target selection.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-top';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorTopEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Authenticated eligible actor callback entry through inline distance, wrapped top-height subtraction, real FixedDiv CALL/RET and signed lower-window comparison. '
      'Equality admits the target; a strictly lower top takes the same rejection decision as the production loop. '
      'The joined rejection theorem connects represented source actor identity, shootability and heights to that original branch and source continuation. '
      'Successful source division, representation and separation remain explicit premises. The rejection epilogue/parent scan, bottom slope, clipping/selection and complete aiming remain open. '
      'No runtime or instruction-semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: eligible actor top slope and rejection decision; strict axiom audit.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify the complete original open-portal aim callback and its saved return frame."""
import argparse,json,re,subprocess
import verify_e1m1_aim_ceiling as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'OriginalAimWindow':['decode_jg','decoded','gate_execution','stop_execution','continue_execution','execution','returned_fields','result_fields','result_saved_regs'],
 'E1M1AimReturnFrame':['ceiling_sp','stack','frame','stack_apart','saved_slot','saved_values'],
 'E1M1AimWindow':['contains_window','contains_ceiling','restored','execution']}

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-window.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate window range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimWindow\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimWindow\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control Collision\nopen E1M1AimWindow (result)\n'
    source+='def code : List UInt8 := ['+','.join(hex(b) for b in raw['aimWindow'])+']\n'
    source+='def continueCode : List UInt8 := ['+','.join(hex(b) for b in raw['aimContinue'])+']\n'
    source+='theorem code_checked : code=OriginalAimWindow.code := by decide\ntheorem continue_checked : continueCode=OriginalAimWindow.continueCode := by decide\ndef linked : X86Routine.Program := fun pc =>\n  match OriginalAimWindow.bytesProgram code continueCode pc with\n  | some op => some op\n  | none => ExtractedAimCeiling.linked pc\ntheorem linked_checked : linked=E1M1AimWindow.program := by\n  unfold linked E1M1AimWindow.program OriginalAimWindow.program\n  rw [code_checked,continue_checked,ExtractedAimCeiling.linked_checked]\n  rfl\n'
    text=(ROOT/'Doom/Proofs/E1M1AimWindow.lean').read_text();a=text.index('theorem execution ')
    decl=text[a:text.index(' := by',a)].replace('theorem execution','theorem execution_checked',1).replace('FloorCaller.cm program','FloorCaller.cm linked')
    source+=decl+' := by\n  rw [linked_checked]\n  exact E1M1AimWindow.execution s f hit line front back ff fc bf bc distance z lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip range eye bottom top pass floorOk ceilingOk returnSafe\n'
    source+='\n'.join('#print axioms '+n for n in ['code_checked','continue_checked','linked_checked','execution_checked'])+'\nend Doom.Verification.ExtractedAimWindow\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimWindow.code_checked'"
    require(marker in output,'missing aim window audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimWindow.'+n for n in ['code_checked','continue_checked','linked_checked','execution_checked']]
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
    previous_cases=previous.cross_check(raw,count)
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for base,size in [(0,0x40000),(0x100000,0x40000),(0x600000,0x1000),(0x700000,0x1000),(0xfffff000,0x1000)]:em.mem_map(base,size)
    for name,pc in [('aimGuard',0x2b760),('aimOpening',0x2b77f),('opening',0x2c340),('aimDistance',0x2b797),('aimFloor',0x2b7a6),('division',0x1d180),('aimCeiling',0x2b7d1),('aimWindow',0x2b800),('aimContinue',0x2b89d)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b7d1);mask=0xffffffff;writes=[];steps=[]
    signed=lambda v:(v&mask) if (v&mask)<2**31 else (v&mask)-2**32
    pack=lambda v:struct.pack('<I',v&mask)
    def code(machine,address,size,data):
        if address==0x12c86d:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,code)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4])))
    groups=dict(equal_floors=0,normal_division=0,saturated_division=0,negative_quotient=0,raised_bound=0,unchanged_bound=0,equal_bound=0,wrapping_stack=0,wrapped_subtraction=0,equal_ceilings=0,ceiling_normal=0,ceiling_saturated=0,ceiling_negative=0,lowered_upper=0,unchanged_upper=0,equal_upper=0,both_divisions=0,negative_distance=0,window_continue=0,window_stop=0,window_equal=0,window_subtraction_overflow=0)
    for case in range(count):
        sp=[0x700800,0,4,16,32,0xfffffff0][case%6]
        before=[rng.getrandbits(32) for _ in regs];before[0]=0x600100;before[4]=sp
        levels=sorted(rng.sample(range(-2147483647,2147483647),4))
        ff,bf=levels[:2];fc,bc=levels[2:]
        if case%2:ff,bf=bf,ff
        if case%4<2:fc,bc=bc,fc
        if case%5==0:bf=ff
        if case%6==0:bc=fc
        bottom=max(ff,bf);top=min(fc,bc);low=min(ff,bf)
        # Product is controlled, while subtraction and division exercise full signed words.
        distance=rng.randint(1,0x7fffffff)*(-1 if case%2 else 1);frac=0x10000;dist=distance
        z=signed(rng.getrandbits(32));num=signed(bottom-z)
        if case%4==0 and ff!=bf:dist=distance=1
        guard=(signed(abs(num)&mask)>>14)<signed(abs(dist)&mask)
        quotient=(abs(num*65536)//abs(dist))*(-1 if (num<0)!=(dist<0) else 1) if guard else (0x7fffffff if (num<0)==(dist<0) else -0x80000000)
        lower=signed(rng.getrandbits(32))
        if case%7==0:lower=quotient
        expected_lower=lower if ff==bf else max(lower,quotient)
        cnum=signed(top-z);cguard=(signed(abs(cnum)&mask)>>14)<signed(abs(dist)&mask)
        cq=(abs(cnum*65536)//abs(dist))*(-1 if (cnum<0)!=(dist<0) else 1) if cguard else (0x7fffffff if (cnum<0)==(dist<0) else -0x80000000)
        upper=signed(rng.getrandbits(32))
        if case%7==0:upper=cq
        expected_upper=upper if fc==bc else min(upper,cq)
        record=struct.pack('<III',frac,1,0x600200)
        em.mem_write(0x600100,record);em.mem_write(0x600210,bytes([rng.randrange(256)|4]))
        em.mem_write(0x600218,struct.pack('<H',case%32768));em.mem_write(0x60022e,pack(0x600300));em.mem_write(0x600232,pack(0x600400))
        for addr,v in [(0x600300,ff),(0x600304,fc),(0x600400,bf),(0x600404,bc),(0x2b9b8,distance),(0x2b9a8,z),(0x2c1e4,lower),(0x2c1e8,upper),(sp,0x12c86d)]:em.mem_write(addr,pack(v))
        for reg,v in zip(regs,before):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear()
        em.emu_start(0x12b760,0x12c86d,count=140)
        require(em.reg_read(x.UC_X86_REG_EIP)==0x12c86d,'ceiling exit mismatch')
        require(len(steps)<=139,'ceiling instruction bound mismatch')
        require(bytes(em.mem_read(0x2c1e4,4))==pack(expected_lower),'lower bound mismatch')
        require(bytes(em.mem_read(0x2c1e8,4))==pack(expected_upper),'upper bound mismatch')
        expected=list(before);expected[0]=int(expected_lower<expected_upper);expected[4]=(sp+4)&mask
        require([em.reg_read(r) for r in regs]==expected,'callback registers not restored')
        require(steps[-1]==(0x12b8a8 if expected_lower<expected_upper else 0x12b819),'wrong callback RET')
        if expected_lower<expected_upper:
            cmp_result=(expected_upper-expected_lower)&mask
            flags=(int((expected_upper&mask)<(expected_lower&mask)) |
              (int(cmp_result==0)<<6) | ((cmp_result>>31)<<7) |
              (int(bool((expected_upper^expected_lower)&(expected_upper^cmp_result)&0x80000000))<<11))
        else:flags=0x40
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'return comparison flags mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        expected_writes+=[((sp-28)&mask,4,0x12b786)]
        expected_writes += [((sp-off)&mask,4,v) for off,v in [(32,before[3]),(36,0x600200),(40,0x600100),(44,before[6])]]
        expected_writes += [(0x2c034,4,top&mask),(0x2c030,4,bottom&mask),(0x2c02c,4,low&mask),(0x2c038,4,(top-bottom)&mask)]
        if ff!=bf:
            expected_writes += [((sp-off)&mask,4,v) for off,v in [(28,0x12b7c4),(32,dist&mask),(36,0x600200),(40,0x600400)]]
            if quotient>lower:expected_writes += [(0x2c1e4,4,quotient&mask)]
            require(0x12b7bf in steps and (0x11d1c0 if guard else 0x11d1b0) in steps,'missing floor division/RET')
        else:require(0x12b7bf not in steps,'equal floors divided')
        if fc!=bc:
            expected_writes += [((sp-off)&mask,4,v) for off,v in [(28,0x12b7f3),(32,dist&mask),(36,0x600200),(40,z&mask)]]
            if cq<upper:expected_writes += [(0x2c1e8,4,cq&mask)]
            require(0x12b7ee in steps and (0x11d1c0 if cguard else 0x11d1b0) in steps,'missing ceiling division/RET')
        else:require(0x12b7ee not in steps,'equal ceilings divided')
        require(steps.count(0x11d180)==int(ff!=bf)+int(fc!=bc),'wrong division count')
        require(writes==expected_writes,'ceiling ordered writes mismatch')
        for addr,v in [(0x2b9a8,z),(0x2b9b8,distance),(sp,0x12c86d)]:require(bytes(em.mem_read(addr,4))==pack(v),'protected word changed')
        groups['equal_floors']+=ff==bf;groups['normal_division']+=ff!=bf and guard;groups['saturated_division']+=ff!=bf and not guard
        groups['negative_quotient']+=ff!=bf and quotient<0;groups['raised_bound']+=expected_lower!=lower;groups['unchanged_bound']+=expected_lower==lower
        groups['equal_bound']+=ff!=bf and lower==quotient;groups['wrapping_stack']+=sp<44;groups['wrapped_subtraction']+=ff!=bf and num!=bottom-z
        groups['equal_ceilings']+=fc==bc;groups['ceiling_normal']+=fc!=bc and cguard;groups['ceiling_saturated']+=fc!=bc and not cguard
        groups['ceiling_negative']+=fc!=bc and cq<0;groups['lowered_upper']+=expected_upper!=upper;groups['unchanged_upper']+=expected_upper==upper
        groups['equal_upper']+=fc!=bc and upper==cq;groups['both_divisions']+=ff!=bf and fc!=bc;groups['negative_distance']+=dist<0
        groups['window_continue']+=expected_lower<expected_upper;groups['window_stop']+=expected_lower>=expected_upper
        groups['window_equal']+=expected_lower==expected_upper
        groups['window_subtraction_overflow']+=signed(expected_upper-expected_lower)!=expected_upper-expected_lower
    require(all(groups.values()),'missing window coverage')
    return dict(cases=count+previous_cases['cases'],previous=previous_cases,window=dict(cases=count,groups=groups),callbacks_or_stubs=False,
      scope='Original open-portal callback from entry through both clipping operations, final signed window branch, six restores and actual return to its caller. All registers and ordered writes checked.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-window';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimWindow'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous open-portal callback through both bound updates, signed window decision and both real return paths. '
      'Saved registers and original caller return word derived from actual prologue and frame preservation. '
      'Entry representation, static separation and source division success remain explicit. '
      'Full source hit-loop correspondence, actors, parent selection continuation and reachable-state discharge remain open. '
      'Decoder adds near JG (0F 8F) using existing signed-branch semantics; runtime and execution semantics unchanged.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original aiming-window decision and both callback returns; strict axiom audit.')
if __name__=='__main__':main()

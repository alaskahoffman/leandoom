#!/usr/bin/env python3
"""Authenticate actor rejection bytes and the source/traversal skip bridge."""
import argparse,json,re,subprocess
import verify_e1m1_aim_line_cycle as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
GROUPS={
 'OriginalAimActorGuard':['decoded','contains_guard','head_execution','flags_execution','self_return_execution','skip_return_execution'],
 'E1M1AimActorSkip':['contains_repeat','contains_actor','contains_guard','returned_fields','callback','execution'],
 'E1M1AimActorSkipJoin':['source','saved_records','execution']}
CALLBACK_ARGS='s f hit pointer who record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter reject'
EXEC_ARGS='s f scene shooter thing path original distance lower upper log work seen visits resolve target sp who fraction j history selection layout bounded empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags ignored stable'
CONTRACTS=[('E1M1AimActorSkip','callback','callback_checked',CALLBACK_ARGS),('E1M1AimActorSkipJoin','execution','skip_checked',EXEC_ARGS)]

def extracted():
    spec,profile,raw=previous.extracted()
    part=json.loads((ROOT/'tests/reference/original-aim-actor-guard.json').read_text())
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    require(not(set(part['units'])&set(spec['units'])),'duplicate actor guard range')
    raw.update(extraction.extract(binary,profile,part))
    return dict(units={**spec['units'],**part['units']}),profile,raw


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorSkipJoin\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorSkip\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1InterceptMark (consume)\nopen E1M1AimCatalog (Portal)\nopen E1M1AimTraversalInvariant (Persistent Next)\nopen E1M1AimSourceCatalog (Represents front back)\nopen E1M1AimIteration\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimRepeatProgram (program)\nopen E1M1AimSynchronizedCycle (AlignedNext)\nopen E1M1AimWall (Safe)\nopen E1M1MinimumScan (address)\nopen E1M1AimPortalPrefix (Position advance Sequence)\nopen E1M1InterceptMinimum (minimum)\n'
    source+='def code : List UInt8 := ['+','.join(hex(b) for b in raw['aimActorGuard'])+']\n'
    source+='theorem code_checked : code=OriginalAimActorGuard.code := by decide\n'
    source+='def linked : X86Routine.Program := fun pc => match E1M1AimRepeatProgram.program pc with | some op => some op | none => OriginalAimActorGuard.bytesProgram code pc\n'
    source+='theorem linked_checked : linked=Doom.Proofs.E1M1AimActorSkip.program := congrArg (fun bytes : List UInt8 => fun pc => match E1M1AimRepeatProgram.program pc with | some op => some op | none => OriginalAimActorGuard.bytesProgram bytes pc) code_checked\n'
    for module,name,checked,args in CONTRACTS:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        decl=re.sub(r'\bprogram\b','linked',decl)
        decl=decl.replace('(returned s)','(Doom.Proofs.E1M1AimActorSkip.returned s)').replace('(result s)','(Doom.Proofs.E1M1AimActorSkip.result s)')
        source+='namespace '+module+'\n'+decl+' := by\n  rw [linked_checked]\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms code_checked\n#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorSkip\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorSkip.code_checked'"
    require(marker in output,'missing actor skip audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorSkip.'+n for n in ['code_checked','linked_checked']]
    names+=['Doom.Verification.ExtractedAimActorSkip.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    for name,pc in [('aimGuard',0x2b760),('aimActorGuard',0x2b81a),('aimStop',0x2b8d2),('interceptGate',0x2c85e)]:em.mem_write(0x100000+pc,raw[name])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    rng=random.Random(0x2b81a);mask=0xffffffff;writes=[];steps=[];stop_at=[None]
    pack=lambda v:struct.pack('<I',v&mask)
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *a:writes.append((a[2],a[3],a[4]&mask)))
    def on_code(machine,address,size,data):
        if address==stop_at[0]:machine.emu_stop()
        else:steps.append(address)
    em.hook_add(u.UC_HOOK_CODE,on_code)
    groups=dict(self_skip=0,unshootable_skip=0,eligible_gate=0,wrapping_stack=0)
    for case in range(count):
        mode=case%3;sp=[0x700800,0,4,8,16,0xfffffff0][(case//3)%6]
        index=case%128;record=0x2ba20+12*index;actor=0x600201+(case%4);who=actor if mode==0 else 0x600301
        before=[rng.getrandbits(32) for _ in regs];before[0]=before[3]=record;before[4]=sp
        flags=rng.randrange(256)&~4
        if mode==2 or mode==0 and case%2:flags|=4
        frac=rng.getrandbits(32);image=struct.pack('<III',frac,0,actor)
        em.mem_write(record,image);em.mem_write(actor+104,bytes([flags]));em.mem_write(0x2b9ac,pack(who))
        cursor=0x2ba20+12*128;em.mem_write(0x2c028,pack(cursor));em.mem_write(sp,pack(0x12c86d))
        bottom,top=rng.getrandbits(32),rng.getrandbits(32)
        em.mem_write(0x2c1e4,pack(bottom));em.mem_write(0x2c1e8,pack(top))
        for reg,val in zip(regs,before):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();steps.clear()
        end=0x12b843 if mode==2 else 0x12c86d;stop_at[0]=end
        em.emu_start(0x12b760,end,count=40)
        expected=list(before)
        if mode==2:expected[1]=actor;expected[2]=record;expected[4]=(sp-24)&mask;expected[6]=who
        else:expected[0]=1;expected[4]=(sp+4)&mask
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'actor guard PC mismatch')
        require([em.reg_read(r) for r in regs]==expected,'actor guard register mismatch')
        require(len(steps)==[22,23,15][mode],'actor guard instruction count mismatch')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c5==(0 if mode==2 else 0x44),'actor guard flags mismatch')
        expected_writes=[((sp-4*(i+1))&mask,4,before[r]) for i,r in enumerate([3,1,2,6,7,5])]
        require(writes==expected_writes,'actor guard stack/write order mismatch')
        require(bytes(em.mem_read(record,12))==image,'callback changed intercept record')
        if mode!=2:
            stop_at[0]=0x12c83a;em.emu_start(end,0x12c83a,count=6)
            expected[1]=cursor
            require(em.reg_read(x.UC_X86_REG_EIP)==0x12c83a,'parent did not continue')
            require([em.reg_read(r) for r in regs]==expected,'parent register mismatch')
            require(len(steps)==[27,28][mode],'parent instruction count mismatch')
            require(writes==expected_writes+[(record,4,0x7fffffff)],'parent sentinel/write order mismatch')
            require(bytes(em.mem_read(record,12))==pack(0x7fffffff)+image[4:],'consumed image mismatch')
        require(bytes(em.mem_read(0x2c1e4,8))==pack(bottom)+pack(top),'aim bounds changed')
        require(bytes(em.mem_read(sp,4))==pack(0x12c86d),'return word changed')
        groups[['self_skip','unshootable_skip','eligible_gate'][mode]]+=1
        if sp<24:groups['wrapping_stack']+=1
    return dict(cases=count,groups=groups,all_registers_flags_and_write_order_checked=True,
      exact_callback_and_parent_instruction_counts=True,unaligned_actor_addresses=True,
      scope='Original actor guard/skip return and parent mark; eligible branch checked only to slope-entry PC, not target arithmetic.')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-skip';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorSkipJoin'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Authenticated actor identity/shootability guards execute from the selected callback through the real RET and parent continuation mark. '
      'The selected shooter or nonshootable actor advances source indices/history without changing aim bounds or portal log; the actual output buffer encodes that consumed history. '
      'New code and its relocation are checked against pinned DOOM.EXE bytes; all existing program ranges are retained. '
      'Actor identity/flag representation, static separation and resolver stability remain premises. The next minimum scan, eligible-target slopes/clipping/selection, whole actor iteration and complete aiming remain open.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: original actor skip guards and consumed-source bridge; strict axiom audit.')
if __name__=='__main__':main()

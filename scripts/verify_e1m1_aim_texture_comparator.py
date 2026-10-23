#!/usr/bin/env python3
"""Complete bounded comparator: inherited authenticated bytes, strict kernel audit."""
import argparse,json,re,subprocess,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_texture_iteration as previous
ROOT,require=previous.ROOT,previous.require
NAMESPACE='Doom.Verification.ExtractedAimTextureComparator'
CONTRACTS=[('gate_nonzero','s f h'),('gate_zero','s f h'),
 ('iteration_continue','s h'),('decrement_measure','v n h'),('loop_exit','n s'),
 ('loop_execution','n s f h'),('iteration_preserved','s r h0 h1 h2 h3'),
 ('loop_memory','n s'),('loop_preserved','n s r h0 h1 h2 h3'),
 ('complete_execution','s f'),('complete_restoration','s safe'),('complete_frame','s'),
 ('table_return','s safe'),('loop_result','n s'),('complete_result','s'),
 ('joined_comparator','pc h'),('joined_table','pc h'),('table_call_return','s f safe')]


def declaration(name):
    source=(ROOT/'Doom/Proofs/OriginalTextureComparator.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={w:'OriginalTextureIteration' for w in ['program','iteration','advanced','foldedPair','prepared']}
    owners.update({w:'OriginalTextureComparator' for w in ['zeroExit','loop','complete','compareBytes','joined']})
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl


def names():
    return [NAMESPACE+'.'+n+'_checked' for n,_ in CONTRACTS]+[
      'Doom.Proofs.OriginalTextureComparator.'+n for n,_ in CONTRACTS]


def certificate(data,raw):
    source='import Doom.Proofs.OriginalTextureComparator\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+previous.previous.HEADER
    cmp='(Doom.Proofs.OriginalTextureIteration.bytesProgram Doom.Verification.ExtractedAimTextureIteration.entry Doom.Verification.ExtractedAimTextureIteration.suffix Doom.Verification.ExtractedAimTextureFold.fold)'
    table='(Doom.Proofs.OriginalTextureTable.bytesProgram Doom.Verification.ExtractedAimTextureTable.table Doom.Verification.ExtractedAimTextureTable.missing)'
    joined='(Doom.Proofs.OriginalTextureComparator.combine '+cmp+' '+table+')'
    for name,args in CONTRACTS:
        decl=declaration(name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.OriginalTextureComparator.joined',joined)
        changed=changed.replace('Doom.Proofs.OriginalTextureIteration.program',cmp).replace('OriginalTextureTable.program',table)
        source+=changed+' := by\n'
        if changed!=decl:
            lemmas=[]
            if cmp in changed:
                lemmas += ['Doom.Verification.ExtractedAimTextureIteration.entry_checked','Doom.Verification.ExtractedAimTextureIteration.suffix_checked','Doom.Verification.ExtractedAimTextureFold.fold_checked']
            if table in changed:
                lemmas += ['Doom.Verification.ExtractedAimTextureTable.table_checked','Doom.Verification.ExtractedAimTextureTable.missing_checked']
            source+='  simp only ['+','.join(lemmas)+'] at *\n'
        source+='  exact Doom.Proofs.OriginalTextureComparator.'+name+' '+args+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'


def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing complete comparator audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def cross_check(raw):
    """Fresh independent CPU executions; the Python model is a test oracle only."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    import verify_e1m1_aim_texture_table as table_evidence
    inherited=previous.cross_check(raw)
    inherited['scope']='Fresh rerun of the predecessor checker: all byte pairs for one iteration and 256 complete calls. Its original first-exit-only theorem boundary is superseded by OriginalTextureComparator; these remain empirical CPU checks.'
    code=raw['entry']+previous.previous.fold_data()[0]['fold']+raw['suffix']
    table=table_evidence.table_data()[0]['table']
    decoder=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for pc,body,count in [(0x4198c,code,33),(0x34700,table,10)]:
        listing=list(decoder.disasm(body,pc))
        require(len(listing)==count and b''.join(bytes(i.bytes) for i in listing)==body,'independent decode mismatch')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    pages=[0,0x30000,0x34000,0x41000,0x600000,0xfffff000]
    for a in pages:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a))
    mask=0xffffffff;rng=random.Random(0x4198d)
    cases=[]
    for joined_call in [False,True]:
        for n in (range(9) if not joined_call else [8]):
            for kind,pos in [('exhaust',None)]+[(k,p) for k in ['mismatch','nul'] for p in range(8)]:
                for mode in ['plain','left_alias','right_alias','wrap_stack','wrap_name']:
                    cases.append((joined_call,n,kind,pos,mode))
    for n in [0x80000000,0xffffffff]:
        for kind in ['mismatch','nul']:
            for pos in range(8):cases.append((False,n,kind,pos,'plain'))
    outcomes={k:0 for k in ['exhaust','mismatch','nul']};counts=set();mismatch8=set();nul8=set()
    total=joined_count=aliases=wrap_stack=wrap_name=large=max_steps=zero_bound=0
    def lower(v):return v+32 if 65<=v<=90 else v
    for joined_call,n,kind,pos,mode in cases:
        mem={a:bytearray(rng.getrandbits(8) for _ in range(4096)) for a in pages}
        def byte(a):return mem[(a&mask)&~4095][a&4095]
        def write_byte(a,v):mem[(a&mask)&~4095][a&4095]=v
        def word(a):return sum(byte(a+j)<<(8*j) for j in range(4))
        def write_word(a,v):
            for j in range(4):write_byte(a+j,(v>>(8*j))&255)
        for pc,body in [(0x4198c,code),(0x34700,table)]:
            for j,b in enumerate(body):write_byte(pc+j,b)
        rr=[rng.getrandbits(32) for _ in regs]
        rr[0]=0x600100;rr[2]=0x600200;rr[3]=n;rr[4]=0 if mode=='wrap_stack' else 0x600800
        incoming_sp=(rr[4]-4)&mask if joined_call else rr[4]
        if mode=='left_alias':rr[0]=(incoming_sp-4)&mask;aliases+=1
        if mode=='right_alias':rr[2]=(incoming_sp-3)&mask;aliases+=1
        if mode=='wrap_name':rr[0]=0xfffffffc;wrap_name+=1
        if mode=='wrap_stack':wrap_stack+=1
        for j in range(8):write_byte(rr[0]+j,65+j);write_byte(rr[2]+j,97+j)
        if kind=='mismatch':write_byte(rr[0]+pos,0x80);write_byte(rr[2]+pos,0xff)
        if kind=='nul':write_byte(rr[0]+pos,0);write_byte(rr[2]+pos,0)
        if joined_call:
            write_word(0x300e0,0x600300);write_word(0x600300,rr[0]);rr[7]=rr[2]
        else:write_word(rr[4],0x34722)
        for a,page in mem.items():em.mem_write(a,bytes(page))
        expected=rr.copy();ordered=[]
        if joined_call:
            expected[6]=0;expected[0]=word(word(0x300e0));expected[3]=8;expected[2]=expected[7]
            expected[4]=(expected[4]-4)&mask;write_word(expected[4],0x34722);ordered.append((expected[4],4,0x34722))
        expected[4]=(expected[4]-4)&mask;write_word(expected[4],expected[1]);ordered.append((expected[4],4,expected[1]))
        consumed=0
        while expected[3]!=0:
            require(consumed<9,'test oracle unexpectedly failed to terminate')
            a,b=lower(byte(expected[0])),lower(byte(expected[2]))
            if a!=b:
                expected[0]=(a-b)&mask;expected[2]=b;outcome='mismatch';break
            if b==0:expected[0]=0;outcome='nul';break
            expected[3]=(expected[3]-1)&mask;expected[0]=(expected[0]+1)&mask;expected[2]=(expected[2]+1)&mask;consumed+=1
        else:expected[0]=0;outcome='exhaust'
        expected[1]=word(expected[4]);expected[4]=(expected[4]+4)&mask
        ret=word(expected[4]);expected[4]=(expected[4]+4)&mask
        require(ret==0x34722,'fixture corrupted return word')
        writes.clear();visits.clear()
        for reg,val in zip(regs,rr):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
        em.emu_start(0x3470c if joined_call else 0x4198c,ret,count=200)
        require([em.reg_read(r) for r in regs]==expected and em.reg_read(x.UC_X86_REG_EIP)==ret,'complete CPU register/return mismatch')
        require(writes==ordered,'ordered stack writes mismatch')
        require(all(bytes(em.mem_read(a,4096))==bytes(page) for a,page in mem.items()),'mapped memory mismatch')
        if outcome!='mismatch':require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,'known zero-result flags mismatch')
        if n<=8:
            require(len(visits)<=22*n+7+(6 if joined_call else 0),'formal instruction budget exceeded')
            counts.add(n)
        else:large+=1
        if n==0:require(0x41995 not in visits,'zero bound read name bytes');zero_bound+=1
        if n==8 and mode=='plain' and outcome=='mismatch':mismatch8.add(consumed)
        if n==8 and mode=='plain' and outcome=='nul':nul8.add(consumed)
        total+=1;joined_count+=int(joined_call);max_steps=max(max_steps,len(visits));outcomes[outcome]+=1
    return dict(inherited_iteration_checks=inherited,complete_cases=total,joined_table_calls=joined_count,
      outcomes=outcomes,bounds=sorted(counts),bound8_mismatch_positions=sorted(mismatch8),
      bound8_nul_positions=sorted(nul8),stack_name_alias_cases=aliases,wrapping_stack_cases=wrap_stack,
      wrapping_name_cases=wrap_name,large_count_early_exits=large,zero_bound_no_name_reads=zero_bound,
      max_observed_instructions=max_steps,all_registers_memory_ordered_writes=True,
      scope='Fresh original CPU calls, all exit positions for bounds 0..8, real table CALL/RET, aliases and wrapping; large counts sampled only on early exits. Formal termination is proved separately for every 32-bit count.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=previous.previous.pinned_data();_,profile,raw=previous.previous.extracted();inputs=previous.iteration_data()
    require(profile['exe_sha256']==inputs[2]['exe_sha256']==mp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-comparator';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalTextureComparator'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    require(not checked.stderr.strip(),'unexpected stderr')
    prior=json.loads((ROOT/'artifacts/e1m1-aim-texture-iteration/report.json').read_text())
    native=None
    if args.cross_check:
        native=cross_check(inputs[0]);(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=prior['units'],
      cells=len(data['cells']),pinned_rows=prior['pinned_rows'],cross_check=native,
      audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),public_theorems=len(CONTRACTS),
      scope='All 32-bit unsigned counts: bound 22*n+7, exact post-PUSH memory-byte result, real ECX/ESP restoration on every exit; actual eight-byte table CALL through RET in <=189 instructions under explicit Apart. Table continuation and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete bounded comparator and actual table CALL/RET; cumulative strict certificate.')
if __name__=='__main__':main()

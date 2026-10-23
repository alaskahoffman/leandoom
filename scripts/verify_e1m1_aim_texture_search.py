#!/usr/bin/env python3
"""Authenticated texture-search repetition, actual restoring return and wrapper."""
import argparse,json,re,subprocess,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_texture_comparator as previous
import verify_e1m1_aim_texture_table as table_evidence
ROOT,require=previous.ROOT,previous.require
NAMESPACE='Doom.Verification.ExtractedAimTextureSearch'
CONTRACTS=[('OriginalTextureSearch',n,a) for n,a in [
 ('branch_execution','s f'),('matched_execution','s f'),('exhausted_execution','s f'),('advance_execution','s f'),
 ('prior_agreement','pc h'),('comparison_registers','s'),('comparison_execution','s f'),('round_execution','s f'),
 ('continuing_round','s go'),('search_descent','n s measure go'),('search_execution','n s f positive measure'),
 ('full_search_execution','s f zero'),('comparison_memory','s'),('comparison_result','s'),('round_memory','s'),
 ('round_frame','s a callSafe pushSafe'),('search_frame','n s f a callSafe pushSafe'),('slot_separation','sp off member'),
 ('terminal_round','s stop'),('search_return','n s f positive measure'),('comparison_ebp','s'),('round_saved','s r h0 h4'),('search_saved','n s f positive measure r h0 h4')]]+[
 ('E1M1AimTextureSearch',n,a) for n,a in [
 ('search_agreement','pc h'),('dash_agreement','pc h'),('table_agreement','pc h'),('wrapper_agreement','pc h'),
 ('lift_run','p exits n s t run agree'),('named_execution','s f named positive'),('named_return','s'),('named_above','s off member'),
 ('inner_return','s f'),('wrapper_words','s f'),('wrapper_execution','s f named positive dest outside ret'),('wrapper_outcomes','s f'),('named_registers','s r h0 h4')]]

def search_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-texture-search.json').read_text());e=table_evidence.extraction_support.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    definitions=re.findall(r'^def (\w+) ',source,re.M)
    for word in definitions:
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+module+'.'+word,decl)
    return decl

def names():
    return [NAMESPACE+'.continuation_checked']+[
        NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
        'Doom.Proofs.'+m+'.'+n for m,n,_ in CONTRACTS]

def certificate(data,raw):
    inputs=search_data()
    source='import Doom.Proofs.E1M1AimTextureSearch\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+table_evidence.HEADER
    source+='def continuation : List UInt8 := ['+','.join(hex(v) for v in inputs[0]['continuation'])+']\n'
    source+='theorem continuation_checked : continuation=OriginalTextureSearch.continuationBytes := by decide +kernel\n'
    cmp='(Doom.Proofs.OriginalTextureIteration.bytesProgram Doom.Verification.ExtractedAimTextureIteration.entry Doom.Verification.ExtractedAimTextureIteration.suffix Doom.Verification.ExtractedAimTextureFold.fold)'
    table='(Doom.Proofs.OriginalTextureTable.bytesProgram Doom.Verification.ExtractedAimTextureTable.table Doom.Verification.ExtractedAimTextureTable.missing)'
    search='(Doom.Proofs.OriginalTextureSearch.bytesProgram '+NAMESPACE+'.continuation Doom.Verification.ExtractedAimTextureDash.restore (Doom.Proofs.OriginalTextureComparator.combine '+cmp+' '+table+'))'
    dash='(Doom.Proofs.OriginalTextureDash.bytesProgram Doom.Verification.ExtractedAimTextureDash.entry Doom.Verification.ExtractedAimTextureDash.restore)'
    wrapper='(Doom.Proofs.OriginalTextureWrapper.bytesProgram Doom.Verification.ExtractedAimTextureWrapper.wrapper)'
    joined='(fun pc => if 0x346f0≤pc ∧ pc<0x34700 then X86ByteRoutine.liftProgram '+dash+' pc else if 0x34750≤pc ∧ pc<0x34773 then X86ByteRoutine.liftProgram '+wrapper+' pc else '+search+' pc)'
    lemmas=[NAMESPACE+'.continuation_checked']+['Doom.Verification.ExtractedAimTexture'+m+'.'+n+'_checked' for m,n in [
        ('Dash','entry'),('Dash','restore'),('Wrapper','wrapper'),('Table','table'),('Table','missing'),('Iteration','entry'),('Iteration','suffix'),('Fold','fold')]]
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.E1M1AimTextureSearch.joined',joined).replace('Doom.Proofs.OriginalTextureSearch.program',search)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:
            used=lemmas if joined in changed else [v for v in lemmas if v not in ['Doom.Verification.ExtractedAimTextureDash.entry_checked','Doom.Verification.ExtractedAimTextureWrapper.wrapper_checked']]
            source+='  simp only ['+','.join(used)+'] at *\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing texture search audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check():
    """Independent CPU executes extracted bytes; Python is only a test oracle."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    iteration=previous.previous.iteration_data()[0]
    inherited=previous.cross_check(iteration)
    dash=table_evidence.previous.dash_data()[0];table=table_evidence.table_data()[0]
    wrapper=table_evidence.wrapper_evidence.wrapper_data()[0]
    ranges=[(0x346f0,dash['entry'],10),(0x34700,table['table'],10),
      (0x34722,search_data()[0]['continuation'],14),(0x3473c,table['missing'],1),
      (0x34741,dash['restore'],6),(0x34750,wrapper['wrapper'],15),
      (0x4198c,iteration['entry']+previous.previous.previous.fold_data()[0]['fold']+iteration['suffix'],33)]
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for pc,body,n in ranges:
        listing=list(dec.disasm(body,pc))
        require(len(listing)==n and b''.join(bytes(i.bytes) for i in listing)==body,'independent decoding mismatch')
    pages=[0,0x30000,0x34000,0x41000,0x600000,0xfffff000]
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for a in pages:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a))
    mask=0xffffffff;rng=random.Random(0x34722)
    cases=[(start,n,match,mode) for start in [0x3470e,0x346f0,0x34750] for n in range(1,5)
        for match in range(-1,n) for mode in ['plain','wrap_stack','name_alias','count_alias','eighth','nul']]
    cases += [(start,1,match,'table_alias') for start in [0x3470e,0x346f0,0x34750] for match in [-1,0]]
    cases += [(0x3470e,0x7fffffff,-1,'signed_limit')]
    stats=dict(cases=0,repeated_cases=0,exhausted_cases=0,matched_cases=0,alias_cases=0,wrapper_cases=0,wrapping_stack_cases=0,count_reload_changed_cases=0,max_comparisons=0,max_instructions=0)
    def lower(v):return v+32 if 65<=v<=90 else v
    def signed(v):return v if v<0x80000000 else v-0x100000000
    def cmpflags(a,b):
        r=(a-b)&mask
        return (0x40 if r==0 else 0)|(0x80 if r>>31 else 0)|(0x800 if ((a^b)&(a^r))>>31 else 0)|(1 if a<b else 0)
    for start,n,match,mode in cases:
        mem={a:bytearray(rng.randbytes(4096)) for a in pages}
        def byte(a):a&=mask;return mem[a&~4095][a&4095]
        def putbyte(a,v):a&=mask;mem[a&~4095][a&4095]=v
        def word(a):return sum(byte(a+j)<<(8*j) for j in range(4))
        def putword(a,v):
            for j in range(4):putbyte(a+j,(v>>(8*j))&255)
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=0 if mode=='wrap_stack' else 0x600800
        inner_sp=(rr[4]-(32 if start==0x34750 else 20 if start==0x346f0 else 0))&mask
        if mode=='count_alias':
            inner_sp=0x300ec;rr[4]=inner_sp+(32 if start==0x34750 else 20 if start==0x346f0 else 0)
        query=(inner_sp-8)&mask if mode=='name_alias' else 0x600100
        rr[0]=query;rr[7]=query;rr[1]=0x7ffffffe if mode=='signed_limit' else 0;rr[6]=0
        tableptr=(inner_sp-4)&mask if mode=='table_alias' else 0x600200
        dest=0x2e483
        putword(rr[4]+(20 if start==0x3470e else 0),dest)
        putword(0x300e0,tableptr);putword(0x300e4,n)
        for j in range(8):putbyte(query+j,97+j)
        if mode=='nul':putbyte(query+3,0)
        for i in range(min(n,4)):
            ptr=0x600300+i*16;putword(tableptr+4*i,ptr)
            for j in range(8):putbyte(ptr+j,65+j)
            if i!=match:putbyte(ptr+(7 if mode=='eighth' else 0),255)
            if mode=='nul':putbyte(ptr+3,0)
        for pc,body,_ in ranges:
            for j,b in enumerate(body):putbyte(pc+j,b)
        for a,page in mem.items():em.mem_write(a,bytes(page))
        initial=rr.copy();ordered=[]
        def push(v):rr[4]=(rr[4]-4)&mask;putword(rr[4],v);ordered.append((rr[4],4,v))
        def pop():v=word(rr[4]);rr[4]=(rr[4]+4)&mask;return v
        if start==0x34750:push(rr[3]);push(rr[2]);rr[2]=rr[0];push(0x34759)
        if start!=0x3470e:
            for r in [3,1,2,6,7]:push(rr[r])
            rr[7]=rr[0];require(byte(rr[0])!=45,'fixture entered dash path')
            rr[2]=word(0x300e4);rr[1]=0
            require(signed(rr[2])>0,'fixture nonpositive initial count');rr[6]=0
        comparisons=0
        while True:
            require(comparisons<10,'unexpected test-oracle iteration count')
            rr[0]=word(0x300e0);rr[3]=8;rr[2]=rr[7];rr[0]=word(rr[6]+rr[0]);push(0x34722);push(rr[1])
            while rr[3]!=0:
                a,b=lower(byte(rr[0])),lower(byte(rr[2]))
                if a!=b:rr[0]=(a-b)&mask;rr[2]=b;break
                if b==0:rr[0]=0;break
                rr[3]-=1;rr[2]=(rr[2]+1)&mask;rr[0]=(rr[0]+1)&mask
            else:rr[0]=0
            rr[1]=pop();require(pop()==0x34722,'helper return corrupted')
            comparisons+=1
            if rr[0]==0:
                rr[0]=rr[1];flags=0x40;outcome='matched';break
            rr[3]=word(0x300e4);rr[1]=(rr[1]+1)&mask;rr[6]=(rr[6]+4)&mask
            flags=cmpflags(rr[1],rr[3])
            if signed(rr[1])>=signed(rr[3]):rr[0]=mask;outcome='exhausted';break
        for r in [7,6,2,1,3]:rr[r]=pop()
        endpoint=pop()
        if start==0x34750:
            require(endpoint==0x34759,'inner lookup return corrupted');rr[3]=rr[0];flags=cmpflags(rr[0],mask)
            if rr[0]==mask:endpoint=0x34760
            else:rr[0]=rr[3];rr[2]=pop();rr[3]=pop();endpoint=pop()
        require(endpoint in [dest,0x34760],'unexpected final endpoint')
        writes.clear();visits.clear()
        for reg,v in zip(regs,initial):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
        em.emu_start(start,endpoint,count=3000)
        require(em.reg_read(x.UC_X86_REG_EIP)==endpoint,'CPU did not reach endpoint')
        require([em.reg_read(r) for r in regs]==rr,'CPU register mismatch')
        require(writes==ordered,'ordered writes mismatch')
        require(all(bytes(em.mem_read(a,4096))==bytes(page) for a,page in mem.items()),'CPU memory mismatch')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'known final flags mismatch')
        require(visits.count(0x4198c)==comparisons,'comparison repetition mismatch')
        require(len(visits)<=202*comparisons+24,'local instruction budget exceeded')
        stats['cases']+=1;stats[outcome+'_cases']+=1;stats['repeated_cases']+=int(comparisons>1)
        stats['alias_cases']+=int('alias' in mode);stats['wrapper_cases']+=int(start==0x34750)
        stats['wrapping_stack_cases']+=int(mode=='wrap_stack')
        stats['count_reload_changed_cases']+=int(mode=='count_alias' and word(0x300e4)!=n)
        stats['max_comparisons']=max(stats['max_comparisons'],comparisons);stats['max_instructions']=max(stats['max_instructions'],len(visits))
    return dict(**stats,all_registers_memory_ordered_writes=True,known_final_flags=True,
        inherited_comparator_checks=inherited,scope='Fresh CPU calls through repeated comparisons, exact lookup epilogues and wrapper return/error-arm entry; aliases and signed INT_MAX endpoint. No I_Error body or reachable startup claim.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=previous.previous.previous.pinned_data();_,profile,raw=previous.previous.previous.extracted()
    inputs=search_data();require(profile['exe_sha256']==inputs[2]['exe_sha256']==mp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-search';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTextureSearch'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=240)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    require(not checked.stderr.strip(),'unexpected stderr')
    prior=json.loads((ROOT/'artifacts/e1m1-aim-texture-comparator/report.json').read_text())
    native=None
    if args.cross_check:
        native=cross_check();(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    units=dict(prior['units']);units.update({'search_'+k:v for k,v in inputs[1].items()})
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=units,
        cells=len(data['cells']),pinned_rows=prior['pinned_rows'],cross_check=native,
        audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),public_theorems=len(CONTRACTS),
        scope='Complete positive named-texture search and wrapper through normal return or error arm 0x34760 (before I_Error); universal signed-index termination even with changing count aliases. Initial positive/named guards are explicit; side loader and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated complete named search, restoring wrapper and strict cumulative certificate.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""All lookup branches and connected side CALLs, pointer emission and latch."""
import argparse,hashlib,json,re,struct,subprocess,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_texture_search as previous
import verify_e1m1_aim_side_textures as caller
ROOT,require=previous.ROOT,previous.require
NAMESPACE='Doom.Verification.ExtractedAimTextureLookup'
CONTRACTS=[('E1M1AimTextureLookup',n,a) for n,a in [
 ('lookup_execution','s f dest outside ret'),('lookup_return','s'),('lookup_registers','s r h0 h4'),
 ('lookup_above','s off member'),('lookup_frame','s a safe'),('inner_return','s f'),('wrapper_words','s f'),
 ('wrapper_execution','s f dest outside ret'),('wrapper_outcomes','s f'),('wrapper_registers','s f success r h0 h4'),('wrapper_frame','s f a safe')]]+[
 ('E1M1AimSideLookup',n,a) for n,a in [
 ('caller_agreement','pc h'),('lookup_agreement','pc h'),('caller_run','exits n s t run'),
 ('first_outcome','s f'),('second_outcome','s f'),('third_outcome','s f'),('execution','s f'),('outcomes','s f'),
 ('call_registers','s f dest ok r h0'),('call_frame','s f dest a safe'),('stage_registers','s f ok r h0'),
 ('registers','s f ok r h0'),('frame','s f ok a safe'),('half_of_load','m a v value'),
 ('post_input','s f ok side index sideBase sectorBase input sourceSafe sectorSafe'),
 ('iteration_caller_agreement','pc h'),('iteration_advance_agreement','pc h'),('iteration_execution','s f'),
 ('returned_pc','s f ok'),('emitted','s f ok side index sideBase sectorBase input sourceSafe sectorSafe'),('body_execution','s f')]]

def declaration(module,name):
    text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
    decl=text[a:a+re.search(r' := by| :=\n',text[a:]).start()]
    owners={n:module for n in re.findall(r'^(?:def|structure) (\w+) ',text,re.M)}
    if module=='E1M1AimTextureLookup':owners['joined']='E1M1AimTextureSearch'
    for word,owner in owners.items():decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def names():
    return [NAMESPACE+'.'+n+'_checked' for n in ['lookupProgram','callerProgram','iterationProgram']]+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+['Doom.Proofs.'+m+'.'+n for m,n,_ in CONTRACTS]

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimSideLookup\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+previous.table_evidence.HEADER
    cmp='(OriginalTextureIteration.bytesProgram Doom.Verification.ExtractedAimTextureIteration.entry Doom.Verification.ExtractedAimTextureIteration.suffix Doom.Verification.ExtractedAimTextureFold.fold)'
    table='(OriginalTextureTable.bytesProgram Doom.Verification.ExtractedAimTextureTable.table Doom.Verification.ExtractedAimTextureTable.missing)'
    search='(OriginalTextureSearch.bytesProgram Doom.Verification.ExtractedAimTextureSearch.continuation Doom.Verification.ExtractedAimTextureDash.restore (OriginalTextureComparator.combine '+cmp+' '+table+'))'
    dash='(OriginalTextureDash.bytesProgram Doom.Verification.ExtractedAimTextureDash.entry Doom.Verification.ExtractedAimTextureDash.restore)'
    wrapper='(OriginalTextureWrapper.bytesProgram Doom.Verification.ExtractedAimTextureWrapper.wrapper)'
    source+='def lookupProgram : X86ByteRoutine.Program := fun pc => if 0x346f0≤pc ∧ pc<0x34700 then X86ByteRoutine.liftProgram '+dash+' pc else if 0x34750≤pc ∧ pc<0x34773 then X86ByteRoutine.liftProgram '+wrapper+' pc else '+search+' pc\n'
    source+='theorem lookupProgram_checked : lookupProgram=E1M1AimTextureSearch.joined := by\n  unfold lookupProgram\n  simp only ['+','.join('Doom.Verification.ExtractedAimTexture'+m+'.'+n+'_checked' for m,n in [
      ('Search','continuation'),('Dash','entry'),('Dash','restore'),('Wrapper','wrapper'),('Table','table'),('Table','missing'),('Iteration','entry'),('Iteration','suffix'),('Fold','fold')])+']\n  rfl\n'
    source+='def callerProgram : X86ByteRoutine.Program := fun pc => if 0x2e47e≤pc ∧ pc<0x2e4af then X86ByteRoutine.liftProgram (OriginalSideTextures.bytesProgram Doom.Verification.ExtractedAimSideTextures.textures) pc else lookupProgram pc\n'
    source+='theorem callerProgram_checked : callerProgram=E1M1AimSideLookup.joined := by\n  unfold callerProgram\n  rw [Doom.Verification.ExtractedAimSideTextures.textures_checked,lookupProgram_checked]\n  rfl\n'
    adv='(OriginalSideAdvance.bytesProgram Doom.Verification.ExtractedSideLoader.publish Doom.Verification.ExtractedSideLoader.link Doom.Verification.ExtractedAimSideAdvance.latch Doom.Verification.ExtractedAimSideAdvance.offsets)'
    source+='def iterationProgram : X86ByteRoutine.Program := fun pc => if pc<0x2e47e ∨ (0x2e4af≤pc ∧ pc<0x2e4dd) then X86ByteRoutine.liftProgram '+adv+' pc else callerProgram pc\n'
    source+='theorem iterationProgram_checked : iterationProgram=E1M1AimSideLookup.iterationProgram := by\n  unfold iterationProgram\n  rw [callerProgram_checked,Doom.Verification.ExtractedSideLoader.publish_checked,Doom.Verification.ExtractedSideLoader.link_checked,Doom.Verification.ExtractedAimSideAdvance.latch_checked,Doom.Verification.ExtractedAimSideAdvance.offsets_checked]\n  rfl\n'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl
        for old,new in [('E1M1AimTextureSearch.joined','lookupProgram'),('E1M1AimSideLookup.joined','callerProgram'),('E1M1AimSideLookup.iterationProgram','iterationProgram')]:
            changed=re.sub(r'(?:Doom\.Proofs\.)?'+re.escape(old),NAMESPACE+'.'+new,changed)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+','.join(NAMESPACE+'.'+n+'_checked' for n in ['lookupProgram','callerProgram','iterationProgram'] if NAMESPACE+'.'+n in changed)+'] at *\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing connected lookup audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def catalog_data():
    """Extract evidence, not a theorem of DOS catalog initialization."""
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    data=(ROOT/sw['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(data).hexdigest()==sw['wad_sha256'],'WAD pin mismatch')
    count,directory=struct.unpack_from('<II',data,4);lumps=[]
    for i in range(count):
        p,n,name=struct.unpack_from('<II8s',data,directory+16*i)
        require(p+n<=len(data),'lump outside WAD');lumps.append((name.rstrip(b'\0').decode('ascii'),data[p:p+n]))
    table=[];hashes={}
    for label in ['TEXTURE1','TEXTURE2']:
        matches=[body for name,body in lumps if name==label]
        if not matches:continue
        require(len(matches)==1,'duplicate texture lump');body=matches[0];hashes[label]=hashlib.sha256(body).hexdigest()
        n=struct.unpack_from('<I',body)[0]
        require(4+4*n<=len(body),'truncated texture offsets')
        for j in range(n):
            p=struct.unpack_from('<I',body,4+4*j)[0];require(p+22<=len(body),'texture descriptor outside lump')
            table.append(body[p:p+8])
    marker=next(i for i,(n,_) in enumerate(lumps) if n=='E1M1')
    label,sides=lumps[marker+3];require(label=='SIDEDEFS' and len(sides)%30==0,'invalid sides')
    hashes['E1M1_SIDEDEFS']=hashlib.sha256(sides).hexdigest()
    queries=[sides[i+off:i+off+8] for i in range(0,len(sides),30) for off in [4,12,20]]
    def folded(b):return bytes(v+32 if 65<=v<=90 else v for v in b).split(b'\0',1)[0]
    mapping={q:(0 if q[0]==45 else next((j for j,t in enumerate(table) if folded(q)==folded(t)),None)) for q in sorted(set(queries))}
    require(all(v is not None for v in mapping.values()),'missing pinned texture name')
    report=dict(wad_sha256=sw['wad_sha256'],lump_sha256=hashes,texture_count=len(table),side_count=len(sides)//30,
      field_count=len(queries),dash_fields=sum(q[0]==45 for q in queries),named_fields=sum(q[0]!=45 for q in queries),
      unique_names=len(mapping),first_match_ids={q.hex():v for q,v in mapping.items()},
      scope='Pinned WAD extraction and host catalog membership only. DOS R_InitTextures execution, allocated pointer-table/image representation and preservation at actual CALLs remain unproved.')
    return table,mapping,report

def cross_check():
    """Execute real side caller and all callee bytes, never mock a return."""
    import itertools,random,capstone,unicorn as u
    from unicorn import x86_const as x
    inherited=previous.cross_check()
    dash=previous.table_evidence.previous.dash_data()[0];table=previous.table_evidence.table_data()[0]
    wrapper=previous.table_evidence.wrapper_evidence.wrapper_data()[0]
    cmp=previous.previous.previous.iteration_data()[0]
    advance=caller.previous.advance_data()[0];side=caller.previous.previous.side_data()[0]
    ranges=[(0x346f0,dash['entry'],10),(0x34700,table['table'],10),(0x34722,previous.search_data()[0]['continuation'],14),
      (0x3473c,table['missing'],1),(0x34741,dash['restore'],6),(0x34750,wrapper['wrapper'],15),
      (0x4198c,cmp['entry']+previous.previous.previous.previous.fold_data()[0]['fold']+cmp['suffix'],33),
      (0x2e47e,caller.texture_data()[0]['textures'],14),(0x2e4af,side['link'],11),(0x2e4d1,advance['latch'],4),(0x2e46a,advance['offsets'],7)]
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for pc,body,n in ranges:
        listing=list(dec.disasm(body,pc));require(len(listing)==n and b''.join(bytes(i.bytes) for i in listing)==body,'independent decoding mismatch')
    pages=[0,0x2c000,0x2e000,0x30000,0x34000,0x41000,0x600000,0x601000,0x602000,0x603000,0xfffff000]
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for a in pages:em.mem_map(a,4096)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    stop_pc=None
    def trace(machine,address,_size,_data):
        # Stop before the endpoint instruction, even when it is a cached block
        # or equals the initial loop header. Do not modify machine state.
        if visits and address==stop_pc:machine.emu_stop()
        else:visits.append(address)
    em.hook_add(u.UC_HOOK_CODE,trace)
    mask=0xffffffff;rng=random.Random(0x2e483)
    stats={n:0 for n in ['cases','dash_lookups','nonpositive_lookups','positive_lookups','complete_three_calls','error_first','error_second','error_third','wrapping_stack_cases','alias_cases','continued_cases','finished_cases','pinned_name_cases','body_cases','max_instructions']}
    actual,names,catalog=catalog_data()
    synthetic=[b'ALPHA\0\0\0',b'BETA\0\0\0\0',b'GAMMA\0\0\0']
    choices=[b'-\0\0\0\0\0\0\0',b'alpha\0\0\0',b'BETA\0\0\0\0',b'MISSING!']
    cases=[(q,mode,synthetic) for q in itertools.product(choices,repeat=3) for mode in ['plain','wrap','field_alias','name_alias','zero','negative']]
    cases += [((q,q,q),'pinned',actual) for q in names]
    def signed(v):return v if v<0x80000000 else v-0x100000000
    def lower(v):return v+32 if 65<=v<=90 else v
    def cmpflags(a,b):
        r=(a-b)&mask
        return (0x40 if r==0 else 0)|(0x80 if r>>31 else 0)|(0x800 if ((a^b)&(a^r))>>31 else 0)|(1 if a<b else 0)
    for serial,(queries,mode,entries) in enumerate(cases):
        mem={a:bytearray(rng.randbytes(4096)) for a in pages}
        def byte(a):a&=mask;return mem[a&~4095][a&4095]
        def putbyte(a,v):a&=mask;mem[a&~4095][a&4095]=v
        def word(a):return sum(byte(a+j)<<(8*j) for j in range(4))
        def putval(a,v,n=4):
            for j in range(n):putbyte(a+j,(v>>(8*j))&255)
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=0 if mode=='wrap' else 0x600f00
        rr[0]=0x600100;rr[7]=0x600110;rr[6]=0x600120;rr[2]=0x600500;rr[3]=0x600600;rr[5]=0;rr[1]=rr[0]
        if mode=='name_alias':rr[0]=rr[4]-24;rr[1]=rr[0]
        if mode=='field_alias':rr[2]=rr[7]-8
        for ptr,q in zip([rr[0],rr[7],rr[6]],queries):
            for j,b in enumerate(q):putbyte(ptr+j,b)
        putval(0x300e0,0x601000);putval(0x300e4,0 if mode=='zero' else mask if mode=='negative' else len(entries))
        putval(0x2c148,0x700000);putval(0x2c11c,1+(serial%2));putval(rr[3]+28,17,2)
        for i,name in enumerate(entries):
            ptr=0x602000+16*i;putval(0x601000+4*i,ptr)
            for j,b in enumerate(name):putbyte(ptr+j,b)
        for pc,body,_ in ranges:
            for j,b in enumerate(body):putbyte(pc+j,b)
        for a,page in mem.items():em.mem_write(a,bytes(page))
        initial=rr.copy();ordered=[];flags=0;lookups=0
        def store(a,v,n=4):v&=(1<<(8*n))-1;putval(a,v,n);ordered.append((a&mask,n,v))
        def push(v):rr[4]=(rr[4]-4)&mask;store(rr[4],v)
        def pop():v=word(rr[4]);rr[4]=(rr[4]+4)&mask;return v
        start=0x2e46a if serial%2==0 else 0x2e47e
        if start==0x2e46a:
            for off in [0,2]:
                v=byte(rr[3]+off)|(byte(rr[3]+off+1)<<8)
                rr[0]=((v if v<32768 else v-65536)<<16)&mask
                store(rr[2]+2*off,rr[0])
            rr[0]=rr[1];stats['body_cases']+=1
        endpoint=None
        for index,(dest,off) in enumerate([(0x2e483,8),(0x2e494,10),(0x2e4a5,12)]):
            if index:rr[0]=rr[7 if index==1 else 6]
            push(dest);push(rr[3]);push(rr[2]);rr[2]=rr[0];push(0x34759)
            for r in [3,1,2,6,7]:push(rr[r])
            rr[7]=rr[0];lookups+=1
            if byte(rr[0])==45:rr[0]=0;stats['dash_lookups']+=1
            else:
                rr[2]=word(0x300e4);rr[1]=0
                if signed(rr[2])<=0:rr[0]=mask;stats['nonpositive_lookups']+=1
                else:
                    rr[6]=0;comparisons=0;stats['positive_lookups']+=1
                    while True:
                        require(comparisons<=len(entries)+1,'oracle search runaway');comparisons+=1
                        rr[0]=word(0x300e0);rr[3]=8;rr[2]=rr[7];rr[0]=word(rr[6]+rr[0]);push(0x34722);push(rr[1])
                        while rr[3]:
                            a,b=lower(byte(rr[0])),lower(byte(rr[2]))
                            if a!=b:rr[0]=(a-b)&mask;rr[2]=b;break
                            if b==0:rr[0]=0;break
                            rr[3]-=1;rr[2]=(rr[2]+1)&mask;rr[0]=(rr[0]+1)&mask
                        else:rr[0]=0
                        rr[1]=pop();require(pop()==0x34722,'comparison return corrupted')
                        if rr[0]==0:rr[0]=rr[1];break
                        rr[3]=word(0x300e4);rr[1]=(rr[1]+1)&mask;rr[6]=(rr[6]+4)&mask
                        if signed(rr[1])>=signed(rr[3]):rr[0]=mask;break
            for r in [7,6,2,1,3]:rr[r]=pop()
            require(pop()==0x34759,'lookup return corrupted');rr[3]=rr[0];flags=cmpflags(rr[0],mask)
            if rr[0]==mask:endpoint=0x34760;stats[['error_first','error_second','error_third'][index]]+=1;break
            rr[0]=rr[3];rr[2]=pop();rr[3]=pop();require(pop()==dest,'wrapper return corrupted')
            if mode=='pinned':require(rr[0]==names[queries[index]],'pinned-name ID mismatch')
            store(rr[4],rr[0]);store(rr[2]+off,rr[0],2)
        if endpoint is None:
            stats['complete_three_calls']+=1
            v=byte(rr[3]+28)|(byte(rr[3]+29)<<8);v=v if v<32768 else v-65536
            rr[0]=(v*86)&mask;rr[5]=(rr[5]+1)&mask;rr[3]=(rr[3]+30)&mask;rr[2]=(rr[2]+18)&mask
            store(rr[4],rr[0]);rr[0]=word(0x2c148);rr[1]=(rr[1]+30)&mask;rr[0]=(rr[0]+word(rr[4]))&mask
            rr[7]=(rr[7]+30)&mask;store(rr[2]-4,rr[0]);rr[0]=word(0x2c11c);rr[6]=(rr[6]+30)&mask
            flags=cmpflags(rr[5],rr[0]);endpoint=0x2e46a if signed(rr[5])<signed(rr[0]) else 0x2e4dd
            stats['continued_cases' if endpoint==0x2e46a else 'finished_cases']+=1
        writes.clear();visits.clear()
        for reg,v in zip(regs,initial):em.reg_write(reg,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
        stop_pc=endpoint
        try:
            em.emu_start(start,0,count=100000)
        except u.UcError as exc:
            raise ValueError(f'CPU case {serial}, mode {mode}, start {start:x}, expected {endpoint:x}, EIP {em.reg_read(x.UC_X86_REG_EIP):x}, recent {[hex(v) for v in visits[-20:]]}') from exc
        require(em.reg_read(x.UC_X86_REG_EIP)==endpoint,'CPU endpoint mismatch')
        require([em.reg_read(r) for r in regs]==rr,f'CPU registers mismatch: {serial} {mode}')
        require(writes==ordered,f'ordered writes mismatch: {serial} {mode}')
        require(all(bytes(em.mem_read(a,4096))==bytes(page) for a,page in mem.items()),'mapped memory mismatch')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==flags,'modeled final flags mismatch')
        require(visits.count(0x34750)==lookups,'lookup count mismatch')
        stats['cases']+=1;stats['wrapping_stack_cases']+=mode=='wrap';stats['alias_cases']+='alias' in mode;stats['pinned_name_cases']+=mode=='pinned'
        stats['max_instructions']=max(stats['max_instructions'],len(visits))
    return dict(**stats,all_registers_memory_ordered_writes=True,known_final_flags=True,catalog=catalog,inherited_search_checks=inherited,
      scope='Fresh actual side CALLs through all real lookup branches, returns, halfword stores, pointer suffix and latch. Pinned-name cases use a constructed catalog image, not DOS initialization. No entry/cleanup, whole side loop or startup completeness claim.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=previous.previous.previous.previous.pinned_data();_,profile,raw=previous.previous.previous.previous.extracted()
    out=ROOT/'artifacts/e1m1-aim-texture-lookup';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTextureLookup','Doom.Proofs.E1M1AimSideLookup'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    prior=json.loads((ROOT/'artifacts/e1m1-aim-texture-search/report.json').read_text());native=None
    if args.cross_check:native=cross_check();(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    catalog=catalog_data()[2];(out/'catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=prior['units'],cells=len(data['cells']),pinned_rows=prior['pinned_rows'],
      audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),public_theorems=len(CONTRACTS),cross_check=native,
      scope='All lookup branches and three actual side CALLs through error or pointer emission/latch. Derived frames/register restoration and post-texture Input. Named catalog success, entry/cleanup, whole side loop and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated all-branch lookup and connected side caller/iteration; strict cumulative audit.')
if __name__=='__main__':main()

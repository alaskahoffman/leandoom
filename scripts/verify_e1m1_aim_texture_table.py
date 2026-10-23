#!/usr/bin/env python3
"""Authenticate original named-texture count gate and comparison entry."""
import argparse,json,re,subprocess
import verify_e1m1_aim_texture_dash as previous
import verify_original_side_loader as extraction_support
import verify_e1m1_aim_side_advance as advance_evidence
import verify_e1m1_aim_side_textures as texture_evidence
import verify_e1m1_aim_texture_wrapper as wrapper_evidence
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
NAMESPACE='Doom.Verification.ExtractedAimTextureTable'
CONTRACTS=[('OriginalTextureTable',n,a) for n,a in [
 ('decoded','pc h'),('gate_execution','s f'),('missing_execution','s f'),
 ('comparison_execution','s f'),('comparison_arguments','s'),('comparison_frame','s a safe'),
 ('gate_and_missing_memory','s f')]]+[
 ('E1M1AimTextureTable',n,a) for n,a in [
 ('empty_restoration','s'),('empty_path','q dashCode tableCode s f named empty dest outside ret'),
 ('first_comparison_path','q dashCode tableCode s f named positive'),('first_arguments','s'),
 ('empty_registers','s'),('empty_frame','s a safe'),('wrapper_empty_path','q dashCode tableCode wrapper s f named empty')]]
GROUPS={m:[n for mm,n,_ in CONTRACTS if m==mm] for m in dict.fromkeys(m for m,_,_ in CONTRACTS)}
REUSED=['Doom.Proofs.E1M1AimTextureWrapper.missing_path','Doom.Proofs.OriginalTextureDash.return_execution','Doom.Proofs.OriginalTextureDash.saved_slots']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={w:'OriginalTextureTable' for w in ['program','listed','count','tested','missing','comparison','firstTexture']}
    owners.update({w:'OriginalTextureDash' for w in ['prepared','nameByte','stackMemory']})
    owners['emptyResult']='E1M1AimTextureTable'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def table_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-texture-table.json').read_text());e=extraction_support.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim,scan,side,advance,textures,wrapper,dash,table):
    units=previous.combined_units(aim,scan,side,advance,textures,wrapper,dash);by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in table.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:require(old==unit,'inconsistent table byte range')
        else:units['table_'+name]=unit;by_offset[unit['code_offset']]=unit
    return units

def names():
    return [NAMESPACE+'.table_checked',NAMESPACE+'.missing_checked']+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
      'Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED

def certificate(data,raw,scan_inputs=None,side_inputs=None,advance_inputs=None,texture_inputs=None,wrapper_inputs=None,dash_inputs=None,table_inputs=None):
    if table_inputs is None:table_inputs=table_data()
    source='import Doom.Proofs.E1M1AimTextureTable\n'+previous.certificate(data,raw,scan_inputs,side_inputs,advance_inputs,texture_inputs,wrapper_inputs,dash_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for name in ['table','missing']:
        source+='def '+name+' : List UInt8 := ['+','.join(hex(v) for v in table_inputs[0][name])+']\n'
        source+='theorem '+name+'_checked : '+name+'=OriginalTextureTable.'+name+'Bytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalTextureTable.bytesProgram '+NAMESPACE+'.table '+NAMESPACE+'.missing)'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=re.sub(r'(?:Doom\.Proofs\.)?OriginalTextureTable\.program',lambda _:machine,decl)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NAMESPACE+'.table_checked,'+NAMESPACE+'.missing_checked] at *\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing table audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,dash,wrapper):
    """Original executions to a real comparison call or missing-result boundary."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x34700);mask=0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0,0x50000);em.mem_map(0x600000,4096)
    for pc,body,n in [(0x34700,raw['table'],10),(0x3473c,raw['missing'],1),(0x346f0,dash['entry'],10),(0x34741,dash['restore'],6),(0x34750,wrapper['wrapper'],15)]:
        em.mem_write(pc,body)
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(body,pc))
        require(len(listing)==n and b''.join(bytes(i.bytes) for i in listing)==body,'independent decode mismatch')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a))
    cases=positive=empty=errors=0
    for start in [0x346f0,0x34750]:
      for alignment in [0,1]:
       for mode in range(3):
        for count in [0,1,2,0x7fffffff,0x80000000,0xffffffff]+[rng.getrandbits(32) for _ in range(10)]:
            pages={a:bytearray(rng.randbytes(4096)) for a in [0x30000,0x600000]}
            def put(a,v):
                for k,b in enumerate((v&mask).to_bytes(4,'little')):pages[(a+k)&~4095][(a+k)&4095]=b
            def get(a):return int.from_bytes(bytes(pages[(a+k)&~4095][(a+k)&4095] for k in range(4)),'little')
            rr=[rng.getrandbits(32) for _ in regs];rr[0]=0x600100;rr[4]=0x600800+alignment
            if mode==2:rr[4]=0x300e4+(32 if start==0x34750 else 20)+alignment;rr[7]=count
            sp=rr[4];dest=[0x2e483,0x2e494,0x2e4a5][cases%3]
            table=(sp-(36 if start==0x34750 else 24)) if mode==1 else 0x600200
            put(0x300e4,count);put(0x300e0,table);put(table,0x600300);put(sp,dest);pages[0x600000][0x100]=0x41
            for a,mem in pages.items():em.mem_write(a,bytes(mem))
            for reg,val in zip(regs,rr):em.reg_write(reg,val)
            em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7);writes.clear();visits.clear();expected=[]
            def push(value):rr[4]-=4;put(rr[4],value);expected.append((rr[4],4,value))
            def pop():v=get(rr[4]);rr[4]+=4;return v
            if start==0x34750:push(rr[3]);push(rr[2]);rr[2]=rr[0];push(0x34759)
            for reg in [3,1,2,6,7]:push(rr[reg])
            rr[7]=rr[0];actual_count=get(0x300e4);rr[2]=actual_count;rr[1]=0
            signed=actual_count if actual_count<0x80000000 else actual_count-0x100000000
            if signed<=0:
                rr[0]=mask
                for reg in [7,6,2,1,3]:rr[reg]=pop()
                endpoint=pop();steps=19;expected_flags=(0x40 if actual_count==0 else 0)|(0x80 if actual_count>>31 else 0)
                empty+=1
                if start==0x34750:
                    require(endpoint==0x34759,'inner return word differs');rr[3]=rr[0]
                    endpoint=0x34760;steps=26;expected_flags=0x40;errors+=1
            else:
                rr[6]=0;rr[0]=get(0x300e0);rr[3]=8;rr[2]=rr[7];rr[0]=get(rr[0]);push(0x34722)
                endpoint=0x4198c;steps=22 if start==0x34750 else 18;expected_flags=0x40;positive+=1
            em.emu_start(start,endpoint,count=steps)
            require(em.reg_read(x.UC_X86_REG_EIP)==endpoint and len(visits)==steps,'endpoint/count mismatch')
            require([em.reg_read(r) for r in regs]==rr,'register mismatch')
            require(writes==expected and all(bytes(em.mem_read(a,4096))==mem for a,mem in pages.items()),'memory/write mismatch')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==expected_flags,'modeled flags differ')
            cases+=1
    return dict(cases=cases,positive_comparison_calls=positive,nonpositive_returns=empty,wrapper_error_entries=errors,
      all_registers=True,ordered_writes=True,mapped_data_memory=True,modeled_flags=True,
      count_read_after_aliased_stack_writes=True,table_entry_read_before_aliased_call_push=True,
      scope='Real named-search initialization and nonpositive-count returns; positive counts stop at the actual comparison CALL. Comparison body, table loop and I_Error are excluded.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted()
    scan=advance_evidence.previous.evidence.scan_data();side=advance_evidence.previous.side_data()
    advance=advance_evidence.advance_data();textures=texture_evidence.texture_data();wrapper=wrapper_evidence.wrapper_data();dash=previous.dash_data();table=table_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan[3]['exe_sha256']==side[2]['exe_sha256']==advance[2]['exe_sha256']==textures[2]['exe_sha256']==wrapper[2]['exe_sha256']==dash[2]['exe_sha256']==table[2]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-table';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan,side,advance,textures,wrapper,dash,table))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTextureTable'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(table[0],dash[0],wrapper[0]) if args.cross_check else None
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=combined_units(spec['units'],scan[1],side[1],advance[1],textures[1],wrapper[1],dash[1],table[1]),
      cells=len(data['cells']),pinned_rows=475,reused_declarations=REUSED,cross_check=native,
      scope='Signed count gate, exact first comparison call, and complete nonpositive-count lookup through wrapper error entry. Name/count read after prologue. Comparison, named-search loop, error body and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: named-texture count gate, first comparison CALL and complete nonpositive return.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Authenticate original no-texture search branch and complete wrapper composition."""
import argparse,json,re,subprocess
import verify_e1m1_aim_texture_wrapper as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
NAMESPACE='Doom.Verification.ExtractedAimTextureDash'
CONTRACTS=[('OriginalTextureDash',n,a) for n,a in [
 ('decoded','pc h'),('entry_execution','s f'),('zero_execution','s f'),
 ('return_execution','s f dest outside ret'),('stack_frame','s a safe'),
 ('return_memory','s f'),('stack_above','s off member'),('saved_slots','s'),('restored_prepared','s')]]+[
 ('E1M1AimTextureDash',n,a) for n,a in [
 ('inner_path','q agree s f dash dest outside ret'),('inner_registers','s'),('inner_frame','s a safe'),
 ('wrapper_path','q agree wrapper s f dash dest outside ret'),('wrapper_registers','s f'),('wrapper_frame','s f a safe')]]
GROUPS={m:[n for mm,n,_ in CONTRACTS if m==mm] for m in dict.fromkeys(m for m,_,_ in CONTRACTS)}
REUSED=['Doom.Proofs.E1M1AimTextureWrapper.caller_path','Doom.Proofs.E1M1AimTextureWrapper.saved_registers','Doom.Proofs.HalfMemory.translate']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={w:'OriginalTextureDash' for w in ['program','listed','prepared','nameByte','gate','zeroed','returned','stackMemory','result']}
    owners.update({w:'E1M1AimTextureDash' for w in ['inner','completed']})
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def dash_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-texture-dash.json').read_text());e=previous.previous.previous.previous.side.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim,scan,side,advance,textures,wrapper,dash):
    units=previous.combined_units(aim,scan,side,advance,textures,wrapper);by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in dash.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:require(old==unit,'inconsistent wrapper byte range')
        else:units['dash_'+name]=unit;by_offset[unit['code_offset']]=unit
    return units

def names():
    return [NAMESPACE+'.entry_checked',NAMESPACE+'.restore_checked']+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
      'Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED

def certificate(data,raw,scan_inputs=None,side_inputs=None,advance_inputs=None,texture_inputs=None,wrapper_inputs=None,dash_inputs=None):
    if dash_inputs is None:dash_inputs=dash_data()
    source='import Doom.Proofs.E1M1AimTextureDash\n'+previous.certificate(data,raw,scan_inputs,side_inputs,advance_inputs,texture_inputs,wrapper_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for name in ['entry','restore']:
        source+='def '+name+' : List UInt8 := ['+','.join(hex(v) for v in dash_inputs[0][name])+']\n'
        source+='theorem '+name+'_checked : '+name+'=OriginalTextureDash.'+name+'Bytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalTextureDash.bytesProgram '+NAMESPACE+'.entry '+NAMESPACE+'.restore)'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=re.sub(r'(?:Doom\.Proofs\.)?OriginalTextureDash\.program',lambda _:machine,decl)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NAMESPACE+'.entry_checked,'+NAMESPACE+'.restore_checked] at *\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing wrapper audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,wrapper):
    """Execute real dash paths through both functions, plus arbitrary epilogues."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x346f0);mask=0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0,0x50000);em.mem_map(0x600000,4096)
    for pc,body,count in [(0x346f0,raw['entry'],10),(0x34741,raw['restore'],6),(0x34750,wrapper['wrapper'],15)]:
        em.mem_write(pc,body)
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(body,pc))
        require(len(listing)==count and b''.join(bytes(i.bytes) for i in listing)==body,'independent decode mismatch')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a))
    cases=success=table=restore=0
    for start in [0x346f0,0x34750,0x34741]:
      for alignment in [0,1]:
       for mode in range(4):
        for trial in range(16):
            mem=bytearray(rng.randbytes(4096));rr=[rng.getrandbits(32) for _ in regs]
            sp=0x600800+alignment;rr[4]=sp;dest=[0x2e483,0x2e494,0x2e4a5][cases%3]
            def initword(a,v):mem[a-0x600000:a+4-0x600000]=v.to_bytes(4,'little')
            if start==0x34741:initword(sp+20,dest)
            else:
                initword(sp,dest);rr[0]=0x600100
                mem[0x100]=0x2d if mode==0 else 0x41
                if mode>=2:
                    rr[0]=sp-(32 if start==0x34750 else 20)
                    mem[rr[0]-0x600000]=0x41 if mode==2 else 0x2d
                    rr[7]=(rr[7]&0xffffff00)|(0x2d if mode==2 else 0x41)
            em.mem_write(0x600000,bytes(mem))
            for reg,val in zip(regs,rr):em.reg_write(reg,val)
            initial=rr[:];flags=0x8d7;em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear();expected=[]
            def push(value):
                rr[4]-=4;initword(rr[4],value);expected.append((rr[4],4,value))
            def pop():
                v=int.from_bytes(mem[rr[4]-0x600000:rr[4]+4-0x600000],'little');rr[4]+=4;return v
            if start==0x34741:
                for reg in [7,6,2,1,3]:rr[reg]=pop()
                endpoint=pop();steps=6;expected_flags=flags;flagmask=0xffffffff;restore+=1
            else:
                if start==0x34750:push(rr[3]);push(rr[2]);rr[2]=rr[0];push(0x34759)
                for reg in [3,1,2,6,7]:push(rr[reg])
                rr[7]=rr[0];byte=mem[rr[0]-0x600000]
                if byte==0x2d:
                    rr[0]=0
                    for reg in [7,6,2,1,3]:rr[reg]=pop()
                    endpoint=pop();steps=16;expected_flags=0x40;flagmask=0x8c1
                    if start==0x34750:
                        require(endpoint==0x34759,'inner return word differs')
                        rr[3]=rr[0];rr[2]=pop();rr[3]=pop();endpoint=pop();steps=27;expected_flags=1
                    success+=1
                else:
                    diff=(byte-0x2d)&255;signed=byte if byte<128 else byte-256
                    expected_flags=(0x80 if diff&128 else 0)|(0x800 if signed-45 < -128 else 0)
                    flagmask=0x8c0;endpoint=0x34700;steps=12 if start==0x34750 else 8;table+=1
            em.emu_start(start,endpoint,count=steps)
            require(em.reg_read(x.UC_X86_REG_EIP)==endpoint and len(visits)==steps,'endpoint/count mismatch')
            require([em.reg_read(r) for r in regs]==rr,'register mismatch')
            require(writes==expected and bytes(em.mem_read(0x600000,4096))==mem,'memory/write mismatch')
            require(em.reg_read(x.UC_X86_REG_EFLAGS)&flagmask==expected_flags&flagmask,'modeled flag mismatch')
            cases+=1
    return dict(cases=cases,dash_successes=success,table_entry_boundaries=table,arbitrary_restore_cases=restore,
      all_registers=True,ordered_writes=True,mapped_data_memory=True,modeled_flags=True,
      name_aliases_saved_edi=True,all_three_caller_continuations=True,
      scope='Original complete dash lookup and wrapper; other names stop at table entry. Shared epilogue also tested from arbitrary saved words. No synthetic helper.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted()
    scan=previous.previous.previous.previous.evidence.scan_data();side=previous.previous.previous.previous.side_data()
    advance=previous.previous.previous.advance_data();textures=previous.previous.texture_data();wrapper=previous.wrapper_data();dash=dash_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan[3]['exe_sha256']==side[2]['exe_sha256']==advance[2]['exe_sha256']==textures[2]['exe_sha256']==wrapper[2]['exe_sha256']==dash[2]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-dash';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan,side,advance,textures,wrapper,dash))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTextureDash'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(dash[0],wrapper[0]) if args.cross_check else None
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=combined_units(spec['units'],scan[1],side[1],advance[1],textures[1],wrapper[1],dash[1]),
      cells=len(data['cells']),pinned_rows=475,reused_declarations=REUSED,cross_check=native,
      scope='Original dash search, common return and complete wrapper path, with all saved-register and word frames discharged for this branch. Dash guard is on post-push memory. Named texture table search, complete loader and startup reachability remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original dash lookup and complete wrapper path, with saved-register and word frames.')
if __name__=='__main__':main()

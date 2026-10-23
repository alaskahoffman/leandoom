#!/usr/bin/env python3
"""Authenticate original texture-wrapper control flow and saved-stack contracts."""
import argparse,json,re,subprocess
import verify_e1m1_aim_side_textures as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
NAMESPACE='Doom.Verification.ExtractedAimTextureWrapper'
CONTRACTS=[('OriginalTextureWrapper',n,a) for n,a in [
 ('decoded','pc h'),('entry_execution','s f'),('gate_execution','s f'),
 ('return_execution','s f dest outside ret'),('entry_arguments','s f'),
 ('entry_frame','s f a ebx edx call'),('return_memory','s f'),('return_registers','s f'),('saved_slots','s f')]]+[
 ('E1M1AimTextureWrapper',n,a) for n,a in [
 ('success_path','q agree s t f g n inner found dest outside ret'),
 ('missing_path','q agree s t f g n inner missing'),
 ('caller_registers','s t stack edx ebx'),('wrapper_frame','s t f a ebx edx call inner'),
 ('caller_path','q agree s t f g n inner found dest outside ret'),('saved_registers','s t f stack edx ebx')]]
GROUPS={m:[n for mm,n,_ in CONTRACTS if m==mm] for m in dict.fromkeys(m for m,_,_ in CONTRACTS)}
REUSED=['Doom.Proofs.OriginalGroupBounds.prefix_join','Doom.Proofs.PlayerHeight.slots_apart']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    for word in ['program','listed','search','choice','result']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.OriginalTextureWrapper.'+word,decl)
    return decl

def wrapper_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-texture-wrapper.json').read_text());e=previous.previous.previous.side.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim,scan,side,advance,textures,wrapper):
    units=previous.combined_units(aim,scan,side,advance,textures);by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in wrapper.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:require(old==unit,'inconsistent wrapper byte range')
        else:units['texture_'+name]=unit;by_offset[unit['code_offset']]=unit
    return units

def names():
    return [NAMESPACE+'.wrapper_checked']+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
      'Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED

def certificate(data,raw,scan_inputs=None,side_inputs=None,advance_inputs=None,texture_inputs=None,wrapper_inputs=None):
    if wrapper_inputs is None:wrapper_inputs=wrapper_data()
    source='import Doom.Proofs.E1M1AimTextureWrapper\n'+previous.certificate(data,raw,scan_inputs,side_inputs,advance_inputs,texture_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='def wrapper : List UInt8 := ['+','.join(hex(v) for v in wrapper_inputs[0]['wrapper'])+']\n'
    source+='theorem wrapper_checked : wrapper=OriginalTextureWrapper.wrapperBytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalTextureWrapper.bytesProgram '+NAMESPACE+'.wrapper)'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=re.sub(r'(?:Doom\.Proofs\.)?OriginalTextureWrapper\.program',lambda _:machine,decl)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NAMESPACE+'.wrapper_checked] at *\n'
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

def cross_check(raw):
    """Execute wrapper segments; never stub or execute the inner name search."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x34750);mask=0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0,0x50000);em.mem_map(0x600000,4096)
    em.mem_write(0x34750,raw['wrapper'])
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['wrapper'],0x34750))
    require(len(listing)==15 and b''.join(bytes(i.bytes) for i in listing)==raw['wrapper'],'independent decode mismatch')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a))
    cases=0
    for start in [0x34750,0x34759]:
      for sp in [0x600800,0x600801]:
       for value in [0,1,65535,65536,0x7fffffff,0x80000000,0xfffffffe,0xffffffff]+[rng.getrandbits(32) for _ in range(24)]:
        mem=bytearray(rng.randbytes(4096));rr=[rng.getrandbits(32) for _ in regs]
        rr[0]=value;rr[4]=sp;dest=[0x2e483,0x2e494,0x2e4a5][cases%3]
        mem[sp+8-0x600000:sp+12-0x600000]=dest.to_bytes(4,'little')
        em.mem_write(0x600000,bytes(mem))
        for reg,val in zip(regs,rr):em.reg_write(reg,val)
        flags=0x8d7;em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear();expected=[]
        def push(value):
            rr[4]-=4;mem[rr[4]-0x600000:rr[4]+4-0x600000]=value.to_bytes(4,'little');expected.append((rr[4],4,value))
        if start==0x34750:
            push(rr[3]);push(rr[2]);rr[2]=rr[0];push(0x34759);endpoint=0x346f0;steps=4
        else:
            rr[3]=rr[0]
            if value==mask:endpoint=0x34760;steps=3
            else:
                rr[2]=int.from_bytes(mem[sp-0x600000:sp+4-0x600000],'little')
                rr[3]=int.from_bytes(mem[sp+4-0x600000:sp+8-0x600000],'little')
                rr[4]+=12;endpoint=dest;steps=7
        em.emu_start(start,endpoint,count=steps)
        require(em.reg_read(x.UC_X86_REG_EIP)==endpoint and len(visits)==steps,'endpoint/count mismatch')
        require([em.reg_read(r) for r in regs]==rr,'register mismatch')
        require(writes==expected and bytes(em.mem_read(0x600000,4096))==mem,'memory/write mismatch')
        actual=em.reg_read(x.UC_X86_REG_EFLAGS)
        if start==0x34750:require(actual==flags,'entry changed flags')
        else:
            signed=lambda v:v if v<0x80000000 else v-0x100000000
            diff=(value-mask)&mask
            expected_flags=(1 if value<mask else 0)|(0x40 if value==mask else 0)|(0x80 if diff>>31 else 0)|(0x800 if signed(value)+1>0x7fffffff else 0)
            require(actual&(1|0x40|0x80|0x800)==expected_flags,'modeled compare flags differ')
        cases+=1
    return dict(cases=cases,all_registers=True,ordered_writes=True,mapped_data_memory=True,
      aligned_and_unaligned_stacks=True,all_three_caller_continuations=True,modeled_flags=True,
      missing_texture_error_boundary=True,scope='Entry and return segments only; inner search and I_Error bodies excluded. No synthetic helper returns.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted()
    scan=previous.previous.previous.evidence.scan_data();side=previous.previous.previous.side_data()
    advance=previous.previous.advance_data();textures=previous.texture_data();wrapper=wrapper_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan[3]['exe_sha256']==side[2]['exe_sha256']==advance[2]['exe_sha256']==textures[2]['exe_sha256']==wrapper[2]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-wrapper';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan,side,advance,textures,wrapper))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTextureWrapper'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(wrapper[0]) if args.cross_check else None
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=combined_units(spec['units'],scan[1],side[1],advance[1],textures[1],wrapper[1]),
      cells=len(data['cells']),pinned_rows=475,reused_declarations=REUSED,cross_check=native,
      scope='Original texture wrapper entry, gate and successful restoring return. Inner search execution and its saved-word/general-word frames remain premises. Missing search result reaches error-path entry. Neither full name lookup nor startup reachability is claimed.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original texture wrapper, exact caller continuation and saved-word restoration.')
if __name__=='__main__':main()

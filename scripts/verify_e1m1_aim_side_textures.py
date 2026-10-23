#!/usr/bin/env python3
"""Authenticate texture caller code and conditional joins to side-pointer emission."""
import argparse,json,re,subprocess
import verify_e1m1_aim_side_advance as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
NAMESPACE='Doom.Verification.ExtractedAimSideTextures'
GROUPS={'OriginalSideTextures':['decoded','first_execution','second_execution','third_execution','finish_execution','return_addresses','arguments','stored_value','stored_frame','first_frame','second_frame','third_frame'],
 'E1M1AimSideTextures':['caller_path','linked_path','caller_frame','caller_encoding','previous_fields','previous_safe']}
CONTRACTS=[('OriginalSideTextures',n,a) for n,a in [('decoded','pc h'),('first_execution','s f'),('second_execution','s f'),('third_execution','s f'),('finish_execution','s f'),('return_addresses','s f'),('arguments','s f'),('stored_value','s off'),('stored_frame','s off a scratch field'),('first_frame','s f a stack'),('second_frame','s f a scratch field stack'),('third_frame','s f a scratch field stack')]]+[
 ('E1M1AimSideTextures',n,a) for n,a in [('caller_path','q agree s a b c f fa fb fc na nb nc lookupA lookupB lookupC'),
 ('linked_path','q agree advance s a b c f fa fb fc na nb nc lookupA lookupB lookupC side sectorIndex sideBase sectorBase input'),
 ('caller_frame','s a b c f fa fb fc address firstSafe secondSafe thirdSafe finalScratch finalField lookupA lookupB lookupC'),
 ('caller_encoding','s a b c f fa fb fc address value image firstSafe secondSafe thirdSafe finalScratch finalField lookupA lookupB lookupC'),
 ('previous_fields','base off member'),('previous_safe','s base sp off member record stack scratch call')]]
REUSED=['Doom.Proofs.HalfMemory.word_frame','Doom.Proofs.HalfMemory.translate','Doom.Proofs.E1M1AimSideAdvance.emitted','Doom.Proofs.OriginalGroupBounds.prefix_join']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={w:'OriginalSideTextures' for w in ['program','listed','firstCall','secondCall','thirdCall','stored','finished']}
    owners.update({'Input':'E1M1AimSideEncoding','sectorAddress':'E1M1AimSideEncoding','Realizes':'E1M1NoiseImage','word':'E1M1NoiseImage','Safe':'E1M1AimSideTextures'})
    for word,owner in owners.items():decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def texture_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-side-textures.json').read_text());e=previous.previous.side.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim,scan,side,advance,textures):
    units=previous.combined_units(aim,scan,side,advance);by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in textures.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:require(old==unit,'inconsistent texture-caller byte range')
        else:units['side_'+name]=unit;by_offset[unit['code_offset']]=unit
    return units

def names():
    return [NAMESPACE+'.textures_checked']+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
      'Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED

def certificate(data,raw,scan_inputs=None,side_inputs=None,advance_inputs=None,texture_inputs=None):
    if texture_inputs is None:texture_inputs=texture_data()
    source='import Doom.Proofs.E1M1AimSideTextures\n'+previous.certificate(data,raw,scan_inputs,side_inputs,advance_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='def textures : List UInt8 := ['+','.join(hex(v) for v in texture_inputs[0]['textures'])+']\n'
    source+='theorem textures_checked : textures=OriginalSideTextures.texturesBytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalSideTextures.bytesProgram '+NAMESPACE+'.textures)'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=re.sub(r'(?:Doom\.Proofs\.)?OriginalSideTextures\.program',lambda _:machine,decl)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NAMESPACE+'.textures_checked] at *\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing texture-caller audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Caller segments only. Helper entries/returns are boundaries, not stubs."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e47e);mask=0xffffffff
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0,0x50000);em.mem_map(0x600000,4096)
    em.mem_write(0x2e47e,raw['textures'])
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['textures'],0x2e47e))
    require(len(listing)==14 and b''.join(bytes(i.bytes) for i in listing)==raw['textures'],'independent decode mismatch')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    # Unicorn may report the full source register for a 16-bit store; compare
    # its written width, and independently compare the resulting memory bytes.
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&((1<<(8*n))-1))))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a))
    cases=0
    for start,off,selector,ret,steps in [(0x2e47e,None,None,0x2e483,1),(0x2e483,8,7,0x2e494,5),(0x2e494,10,6,0x2e4a5,5),(0x2e4a5,12,None,None,3)]:
      for mode in range(4):
       for value in [0,1,65535,65536,0x80000000,0xffffffff]+[rng.getrandbits(32) for _ in range(18)]:
        mem=bytearray(rng.randbytes(4096));rr=[rng.getrandbits(32) for _ in regs]
        rr[0]=value;rr[2]=0x600401;rr[4]=0x600801
        if mode==1:rr[2]=rr[4]-(off or 0)
        if mode==2:rr[2]=rr[4]-4-(off or 0)
        if mode==3:rr[4]=0x600805;rr[2]=rr[4]-1-(off or 0)
        em.mem_write(0x600000,bytes(mem))
        for reg,val in zip(regs,rr):em.reg_write(reg,val)
        flags=0x8d7;em.reg_write(x.UC_X86_REG_EFLAGS,flags);writes.clear();visits.clear();expected=[]
        def put(a,v,n):
            v &= (1<<(8*n))-1
            mem[a-0x600000:a-0x600000+n]=v.to_bytes(n,'little');expected.append((a,n,v))
        if off is not None:
            put(rr[4],rr[0],4);put(rr[2]+off,rr[0],2)
        if selector is not None:rr[0]=rr[selector]
        if ret is not None:rr[4]-=4;put(rr[4],ret,4)
        endpoint=0x34750 if ret is not None else 0x2e4af
        em.emu_start(start,endpoint,count=steps)
        require(em.reg_read(x.UC_X86_REG_EIP)==endpoint and len(visits)==steps,'endpoint/count mismatch')
        require([em.reg_read(r) for r in regs]==rr,'register mismatch')
        require(writes==expected,f'ordered write mismatch at {start:x}, mode {mode}, value {value:x}: {writes} != {expected}')
        require(bytes(em.mem_read(0x600000,4096))==mem,f'memory mismatch at {start:x}, mode {mode}, value {value:x}')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)==flags,'caller changed flags')
        cases+=1
    return dict(cases=cases,segments=4,all_registers=True,flags_preserved=True,ordered_writes=True,mapped_data_memory=True,
      low_halfword_truncation=True,overlapping_scratch_field_and_return_slots=True,
      scope='Original caller segments only; lookup function is never executed or replaced by a stub. No whole-loader claim.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();scan=previous.previous.evidence.scan_data();side=previous.previous.side_data();advance=previous.advance_data();textures=texture_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan[3]['exe_sha256']==side[2]['exe_sha256']==advance[2]['exe_sha256']==textures[2]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-side-textures';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan,side,advance,textures))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSideTextures'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(textures[0]) if args.cross_check else None
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=combined_units(spec['units'],scan[1],side[1],advance[1],textures[1]),
      cells=len(data['cells']),pinned_rows=475,reused_declarations=REUSED,cross_check=native,
      scope='Three exact texture CALLs and their caller-side continuations. Conditional actual helper paths compose through the sector-pointer suffix and latch. Caller preservation reduced to stack separation and helper word frames; texture helper bodies and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated texture caller, conditional lookup-path join and prior-pointer frame.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Authenticate the side-loader loop test and preservation into the next record."""
import argparse,json,re,subprocess
import verify_e1m1_aim_side_encoding as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
NAMESPACE='Doom.Verification.ExtractedAimSideAdvance'
GROUPS={'OriginalSideAdvance':['decoded','latch_execution','offsets_execution','original_agrees','linked_execution','continued_execution','memory','offsets_frame'],
 'E1M1AimSideAdvance':['progress','exit_pc','count_preserved','bounded_branch','emitted','next_offsets_preserve','continuing_emitted','bounded_continuation','bounded_finished']}
CONTRACTS=[('OriginalSideAdvance',n,a) for n,a in [('decoded','pc h'),('latch_execution','s f'),('offsets_execution','s f'),('original_agrees','pc h'),('linked_execution','s f'),('continued_execution','s f next'),('memory','s'),('offsets_frame','s a firstSafe secondSafe')]]+[
 ('E1M1AimSideAdvance',n,a) for n,a in [('progress','s'),('exit_pc','s'),('count_preserved','s scratchSafe pointerSafe'),
 ('bounded_branch','s i total index count small inside scratchSafe pointerSafe'),('emitted','s f side index sideBase sectorBase input'),
 ('next_offsets_preserve','s'),('continuing_emitted','s f side index sideBase sectorBase input next'),
 ('bounded_continuation','s f side sectorIndex i total sideBase sectorBase input index count small more scratchSafe pointerSafe'),
 ('bounded_finished','s f side sectorIndex i total sideBase sectorBase input index count small last scratchSafe pointerSafe')]]
REUSED=['Doom.Proofs.OriginalSideLoader.link_execution','Doom.Proofs.E1M1AimSideEncoding.link_encoding','Doom.Proofs.PlayerHeight.slots_apart']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'result':'OriginalSideAdvance','prepared':'OriginalSideAdvance','advanced':'OriginalSideAdvance','program':'OriginalSideAdvance','listed':'OriginalSideAdvance',
      'Input':'E1M1AimSideEncoding','sectorAddress':'E1M1AimSideEncoding','Realizes':'E1M1NoiseImage','word':'E1M1NoiseImage'}
    for word,owner in owners.items():decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def advance_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-side-advance.json').read_text());e=previous.side.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim,scan,side,advance):
    units=previous.combined_units(aim,scan,side);by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in advance.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:require(old==unit,'inconsistent side-advance byte range')
        else:units['side_'+name]=unit;by_offset[unit['code_offset']]=unit
    return units

def names():
    return [NAMESPACE+'.'+n+'_checked' for n in ['latch','offsets']]+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
      'Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED

def certificate(data,raw,scan_inputs=None,side_inputs=None,advance_inputs=None):
    if advance_inputs is None:advance_inputs=advance_data()
    source='import Doom.Proofs.E1M1AimSideAdvance\n'+previous.certificate(data,raw,scan_inputs,side_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for name,bs in advance_inputs[0].items():
        source+='def '+name+' : List UInt8 := ['+','.join(hex(v) for v in bs)+']\n'
        source+='theorem '+name+'_checked : '+name+'=OriginalSideAdvance.'+name+'Bytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalSideAdvance.bytesProgram Doom.Verification.ExtractedSideLoader.publish Doom.Verification.ExtractedSideLoader.link '+NAMESPACE+'.latch '+NAMESPACE+'.offsets)'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        # Both fully qualified and locally qualified uses occur in signatures.
        changed=re.sub(r'(?:Doom\.Proofs\.)?OriginalSideAdvance\.program',lambda _:machine,decl)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  rw [Doom.Verification.ExtractedSideLoader.publish_checked,Doom.Verification.ExtractedSideLoader.link_checked,'+NAMESPACE+'.latch_checked,'+NAMESPACE+'.offsets_checked]\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing side-advance audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw,side_raw):
    """Independent x86 execution, including aliases that invalidate nice inputs."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x2e4d1);mask=0xffffffff;CODE=0x100000
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(CODE,0x40000)
    for name,pc,count in [('latch',0x2e4d1,4),('offsets',0x2e46a,7)]:
        listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw[name],pc))
        require(len(listing)==count and b''.join(bytes(i.bytes) for i in listing)==raw[name],'independent decode mismatch')
        em.mem_write(CODE+pc,raw[name])
    em.mem_write(CODE+0x2e4af,side_raw['link'])
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    pages=[0x2c000,0x600000]
    for a in pages:em.mem_map(a,4096)
    writes=[];visits=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&mask)))
    em.hook_add(u.UC_HOOK_CODE,lambda _e,a,_n,_d:visits.append(a-CODE))
    signed=lambda v:v if v<2**31 else v-2**32
    continued=finished=0
    edges=[(0,2),(0,1),(0xffffffff,1),(0x7fffffff,1),(0,0xffffffff),(0x80000000,0x80000002),(0x7ffffffe,0x7fffffff),(1,0)]
    for mode in range(6):
      for counter,count in edges:
       for index in [0,84,32767,32768,65535]:
        mem={a:bytearray(rng.randbytes(4096)) for a in pages};expected_writes=[]
        def put(a,v,n=4,record=False):
            bs=(v&((1<<(8*n))-1)).to_bytes(n,'little')
            for k,b in enumerate(bs):mem[(a+k)&~4095][(a+k)&4095]=b
            if record:expected_writes.append((a,n,v&mask))
        def get(a,n=4):return int.from_bytes(bytes(mem[(a+k)&~4095][(a+k)&4095] for k in range(n)),'little')
        rr=[rng.getrandbits(32) for _ in regs];rr[2]=0x600401;rr[3]=0x600201;rr[4]=0x600801;rr[5]=counter
        if mode==1:rr[4]=0x2c11c
        if mode==2:rr[2]=0x2c11c-14
        if mode==3:rr[3]=rr[2]-14
        if mode==4:rr[4]=0x2c148
        if mode==5:rr[4]=rr[2]+14
        put(0x2c11c,count);put(0x2c148,0x600a00);put(rr[3]+28,index,2)
        for a,b in mem.items():em.mem_write(a,bytes(b))
        for reg,val in zip(regs,rr):em.reg_write(reg,val)
        em.reg_write(x.UC_X86_REG_EFLAGS,2);writes.clear();visits.clear()
        off=((index if index<32768 else index-65536)*86)&mask
        put(rr[4],off,record=True)
        target=(get(0x2c148)+off)&mask
        put(rr[2]+14,target,record=True)
        rr[0]=get(0x2c11c);rr[5]=(rr[5]+1)&mask;rr[3]=(rr[3]+30)&mask;rr[2]=(rr[2]+18)&mask
        rr[1]=(rr[1]+30)&mask;rr[7]=(rr[7]+30)&mask;rr[6]=(rr[6]+30)&mask
        more=signed(rr[5])<signed(rr[0]);exit_pc=0x2e47e if more else 0x2e4dd
        if more:
            # Shift by 16 preserves the low halfword regardless of sign extension.
            put(rr[2],(get(rr[3],2)<<16)&mask,record=True)
            put(rr[2]+4,(get(rr[3]+2,2)<<16)&mask,record=True)
            rr[0]=rr[1];continued+=1
        else:finished+=1
        em.emu_start(CODE+0x2e4af,CODE+exit_pc,count=22)
        require(em.reg_read(x.UC_X86_REG_EIP)==CODE+exit_pc,'endpoint mismatch')
        require(len(visits)==(22 if more else 15),'instruction count mismatch')
        require(writes==expected_writes,'ordered writes mismatch')
        require([em.reg_read(r) for r in regs]==rr,'register mismatch')
        require(all(bytes(em.mem_read(a,4096))==b for a,b in mem.items()),'memory mismatch')
    require(continued>0 and finished>0,'branch coverage')
    return dict(cases=continued+finished,continued=continued,finished=finished,all_registers=True,
      ordered_writes=True,mapped_memory=True,signed_overflow_edges=True,count_and_sector_global_aliases=True,
      next_offset_source_destination_alias=True,scope='Local 15/22-instruction runs, not full startup. Flags are modeled only where needed by the branch; not compared as a complete hardware flag state.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();scan=previous.evidence.scan_data();side=previous.side_data();advance=advance_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan[3]['exe_sha256']==side[2]['exe_sha256']==advance[2]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-side-advance';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan,side,advance))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSideAdvance'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(advance[0],side[0]) if args.cross_check else None
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=combined_units(spec['units'],scan[1],side[1],advance[1]),
      cells=len(data['cells']),pinned_rows=475,reused_declarations=REUSED,cross_check=native,
      scope='Actual side-pointer suffix joined to signed loop latch and next offset stores. Just-emitted pointer survives without extra frame premises. Finite-count branch requires count preservation and signed bounds. Texture calls, enclosing loader and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: side-pointer suffix, actual loop decision and next offset writes; strict inherited audit.')
if __name__=='__main__':main()

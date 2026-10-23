#!/usr/bin/env python3
"""Authenticated comparator iteration; cumulative kernel certificate and x86 checks."""
import argparse,hashlib,json,re,subprocess,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_texture_fold as previous
ROOT,require=previous.ROOT,previous.require
NAMESPACE='Doom.Verification.ExtractedAimTextureIteration'
CONTRACTS=[('loads_execution','s f'),('decoded','pc h'),('suffix_execution','s'),
 ('fold_code','pc h'),('iteration_execution','s f'),('iteration_memory','s'),
 ('loaded_values','s'),('loaded_fold_values','s'),('folded_other_registers','s r other'),
 ('mismatch_value','s'),('restore_execution','s f'),('iteration_return','s f done'),
 ('entry_execution','s f nonzero'),('first_iteration_return','s f nonzero done'),
 ('iteration_stack','s'),('first_restoration','s safe'),('caller_return','s f nonzero done safe returnWord'),
 ('table_first_return','s done safe')]
SEMANTICS=['Doom.Verification.X86ByteRoutine.'+n for n in
 ['Prefix.run','run_mono','run_path','Prefix.transfer','Prefix.finish','Prefix.trans']]+['Doom.Verification.X86ComparatorRoutine.decrement_core']

def iteration_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-texture-iteration.json').read_text())
    e=previous.extraction_support.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def declaration(name):
    source=(ROOT/'Doom/Proofs/OriginalTextureIteration.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    for word in ['program','listed','loaded','mismatch','advanced','suffix','foldedPair','iteration','restored','prepared']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.OriginalTextureIteration.'+word,decl)
    return decl

def names():
    return [NAMESPACE+'.'+u+'_checked' for u in ['entry','suffix']]+[
      NAMESPACE+'.'+n+'_checked' for n,_ in CONTRACTS]+[
      'Doom.Proofs.OriginalTextureIteration.'+n for n,_ in CONTRACTS]+SEMANTICS

def certificate(data,raw,inputs=None):
    if inputs is None:inputs=iteration_data()
    source='import Doom.Proofs.OriginalTextureIteration\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+previous.HEADER
    for unit,bs in inputs[0].items():
        source+='def '+unit+' : List UInt8 := ['+','.join(hex(v) for v in bs)+']\n'
        source+='theorem '+unit+'_checked : '+unit+'=OriginalTextureIteration.'+unit+'Bytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalTextureIteration.bytesProgram '+NAMESPACE+'.entry '+NAMESPACE+'.suffix Doom.Verification.ExtractedAimTextureFold.fold)'
    for name,args in CONTRACTS:
        decl=declaration(name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.OriginalTextureIteration.program',machine)
        source+=changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NAMESPACE+'.entry_checked,'+NAMESPACE+'.suffix_checked,Doom.Verification.ExtractedAimTextureFold.fold_checked] at *\n'
        source+='  exact Doom.Proofs.OriginalTextureIteration.'+name+' '+args+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing iteration audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x41995);mask=0xffffffff
    code=raw['entry']+previous.fold_data()[0]['fold']+raw['suffix']
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(code,0x4198c))
    require(len(listing)==33 and b''.join(bytes(i.bytes) for i in listing)==code,'independent decoding failed')
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for addr in [0,0x34000,0x41000,0x600000,0xfffff000]:em.mem_map(addr,4096)
    em.mem_write(0x4198c,code)
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,addr,size,value,_d:writes.append((addr,size,value)))
    stops=set()
    em.hook_add(u.UC_HOOK_CODE,lambda e,a,_s,_d:e.emu_stop() if a in stops else None)
    def lower(v):return v+32 if 65<=v<=90 else v
    def run(rr,start,end,budget):
        writes.clear()
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
        em.emu_start(start,end,count=budget)
        return [em.reg_read(r) for r in regs]
    outcomes={'mismatch':0,'zero':0,'continue':0}
    stops.update([0x419cc,0x4198d])
    for a in range(256):
      for b in range(256):
        rr=[rng.getrandbits(32) for _ in regs]
        rr[0]=0xffffffff if b%2 else 0x600100;rr[2]=0 if a%2 else 0x600200
        em.mem_write(rr[0],bytes([a]));em.mem_write(rr[2],bytes([b]))
        expected=rr.copy();aa,bb=lower(a),lower(b);expected[1]=(rr[1]&0xffff0000)|(bb<<8)|aa
        if aa!=bb:
            expected[0]=(aa-bb)&mask;expected[2]=bb;pc=0x419cc;outcomes['mismatch']+=1
        elif bb==0:
            expected[0]=0;pc=0x419cc;outcomes['zero']+=1
        else:
            expected[0]=(rr[0]+1)&mask;expected[2]=(rr[2]+1)&mask;expected[3]=(rr[3]-1)&mask;pc=0x4198d;outcomes['continue']+=1
        actual=run(rr,0x41995,0,21)
        require(actual==expected and em.reg_read(x.UC_X86_REG_EIP)==pc,'iteration result mismatch')
        require(not writes,'iteration wrote memory')
        if aa==bb==0:require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,'zero exit flags mismatch')
    # Independent bounded complete calls (empirical only beyond the proved first exit).
    stops.clear();full=0;alias_cases=0
    for i in range(256):
        data=bytearray(rng.getrandbits(8) for _ in range(4096));base=0x600000;sp=base+0x800
        rr=[rng.getrandbits(32) for _ in regs];rr[0]=base+0x100;rr[2]=base+0x200;rr[3]=i%9;rr[4]=sp
        for j in range(8):
            data[0x100+j]=65+j;data[0x200+j]=97+j
        if i%4==0:data[0x200+i%8]=255
        if i%4==1:data[0x100+i%8]=data[0x200+i%8]=0
        if i%8==2:rr[0]=sp-4;alias_cases+=1
        if i%8==3:rr[2]=sp-3;alias_cases+=1
        data[0x800:0x804]=(0x34722).to_bytes(4,'little');em.mem_write(base,bytes(data))
        expected=rr.copy();data[0x7fc:0x800]=rr[1].to_bytes(4,'little')
        while expected[3]!=0:
            a=lower(data[expected[0]-base]);b=lower(data[expected[2]-base])
            if a!=b:expected[0]=(a-b)&mask;expected[2]=b;break
            if b==0:expected[0]=0;break
            expected[3]-=1;expected[2]+=1;expected[0]+=1
        else:expected[0]=0
        expected[4]=sp+4
        actual=run(rr,0x4198c,0x34722,200)
        require(actual==expected and em.reg_read(x.UC_X86_REG_EIP)==0x34722,'complete call mismatch')
        require(bytes(em.mem_read(base,4096))==bytes(data),'complete data-memory mismatch')
        require(writes==[(sp-4,4,rr[1])],'ordered stack writes mismatch')
        full+=1
    require(bytes(em.mem_read(0x4198c,len(code)))==code,'code modified')
    return dict(iteration_cases=sum(outcomes.values()),outcomes=outcomes,complete_call_cases=full,
      stack_name_alias_cases=alias_cases,all_registers=True,iteration_no_writes=True,
      complete_call_memory_and_ordered_writes=True,wrapping_pointer_cases=True,
      flags='Check known zero-exit flags; SUB/INC/DEC flags are conservatively forgotten in the formal model.',
      scope='All byte pairs for one actual iteration; 256 empirical complete calls with bounds 0..8. Full bounded-loop termination is NOT a theorem in this milestone.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=previous.pinned_data();_,profile,raw=previous.extracted();inputs=iteration_data()
    require(profile['exe_sha256']==inputs[2]['exe_sha256']==mp['exe_sha256'],'executable mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-iteration';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,inputs))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalTextureIteration'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    require(not checked.stderr.strip(),'unexpected stderr')
    prior=json.loads((out/'prior-fold-evidence/report.json').read_text())
    units=dict(prior['units'])
    for name,unit in inputs[1].items():
        require(all(v['code_offset']!=unit['code_offset'] for v in units.values()),'duplicate range')
        units['iteration_'+name]=unit
    native=None
    if args.cross_check:
        native=cross_check(inputs[0]);(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=units,
      cells=len(data['cells']),pinned_rows=prior['pinned_rows'],cross_check=native,
      audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),
      scope='Complete load/fold/CMP/suffix iteration, memory and stack preservation; first-exit actual POP/RET to caller under explicit conditions. General bounded termination and lookup continuation remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete original comparator iteration; cumulative strict certificate.')
if __name__=='__main__':main()

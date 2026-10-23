#!/usr/bin/env python3
"""Authenticate original byte-register ASCII folding in the bounded name comparator."""
import argparse,json,re,subprocess
import verify_e1m1_aim_texture_table as previous
import verify_e1m1_aim_texture_dash as dash_evidence
import verify_original_side_loader as extraction_support
import verify_e1m1_aim_side_advance as advance_evidence
import verify_e1m1_aim_side_textures as texture_evidence
import verify_e1m1_aim_texture_wrapper as wrapper_evidence
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
NAMESPACE='Doom.Verification.ExtractedAimTextureFold'
CONTRACTS=[('OriginalTextureFold',n,a) for n,a in [
 ('decoded','pc h'),('cl_execution','s f'),('ch_execution','s f'),('compare_execution','s f'),
 ('lowercase_spec','b'),('lower_idempotent','b'),('fold_memory','s r'),
 ('fold_other_registers','s r q other'),('cl_value','s'),('ch_value','s'),('pair_values','s')]]
SEMANTICS=[('execute_base','op s'),('run_lift','p exits fuel s'),
 ('run_sound','actual listed sound exits fuel s valid'),('byte_memory','s r t v')]
GROUPS={'OriginalTextureFold':[n for _,n,_ in CONTRACTS]}
REUSED=['Doom.Proofs.write_low_read','Doom.Proofs.write_high_read']

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    for word in ['program','listed','clResult','chResult','compared','lower','folded']:
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.OriginalTextureFold.'+word,decl)
    return decl

def fold_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    spec=json.loads((ROOT/'tests/reference/original-texture-fold.json').read_text());e=extraction_support.extraction
    binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    return e.extract(binary,profile,spec),spec['units'],profile

def combined_units(aim,scan,side,advance,textures,wrapper,dash,table,fold):
    units=previous.combined_units(aim,scan,side,advance,textures,wrapper,dash,table)
    for name,unit in fold.items():
        require(all(u['code_offset']!=unit['code_offset'] for u in units.values()),'duplicate fold range')
        units['fold_'+name]=unit
    return units

def names():
    return [NAMESPACE+'.fold_checked']+[
      NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+[
      'Doom.Proofs.'+m+'.'+n for m,n,_ in CONTRACTS]+[
      'Doom.Verification.X86ByteRoutine.'+n for n,_ in SEMANTICS]+REUSED

def certificate(data,raw,scan_inputs=None,side_inputs=None,advance_inputs=None,texture_inputs=None,wrapper_inputs=None,dash_inputs=None,table_inputs=None,fold_inputs=None):
    if fold_inputs is None:fold_inputs=fold_data()
    source='import Doom.Proofs.OriginalTextureFold\n'+previous.certificate(data,raw,scan_inputs,side_inputs,advance_inputs,texture_inputs,wrapper_inputs,dash_inputs,table_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='def fold : List UInt8 := ['+','.join(hex(v) for v in fold_inputs[0]['fold'])+']\n'
    source+='theorem fold_checked : fold=OriginalTextureFold.foldBytes := by decide +kernel\n'
    machine='(Doom.Proofs.OriginalTextureFold.bytesProgram '+NAMESPACE+'.fold)'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=re.sub(r'(?:Doom\.Proofs\.)?OriginalTextureFold\.program',lambda _:machine,decl)
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  simp only ['+NAMESPACE+'.fold_checked] at *\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing fold audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(raw):
    """Execute original blocks for every byte pair; check full registers and modeled flags."""
    import random,capstone,unicorn as u
    from unicorn import x86_const as x
    rng=random.Random(0x41999)
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32);em.mem_map(0x41000,4096);em.mem_write(0x41999,raw['fold'])
    listing=list(capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32).disasm(raw['fold'],0x41999))
    require(len(listing)==11 and b''.join(bytes(i.bytes) for i in listing)==raw['fold'],'decode mismatch')
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    writes=[];em.hook_add(u.UC_HOOK_MEM_WRITE,lambda *args:writes.append(args[2:5]))
    def lower(b):return b+32 if 65<=b<=90 else b
    def flags(a,b,add=False):
        v=(a+b if add else a-b)&255
        of=((a^b)&128==0 and (v^a)&128!=0) if add else ((a^b)&128!=0 and (v^a)&128!=0)
        cf=(a+b>255) if add else a<b
        return (0x40 if v==0 else 0)|(v&128)|(0x800 if of else 0)|int(cf)
    cases=0
    for start,end,mode in [(0x41999,0x419a6,'cl'),(0x419a6,0x419b3,'ch'),(0x41999,0x419b5,'pair')]:
      for a in range(256):
       for b in (range(256) if mode=='pair' else [rng.randrange(256)]):
        rr=[rng.getrandbits(32) for _ in regs];rr[1]=(rr[1]&0xffff0000)|(b<<8)|a
        expected=rr.copy();aa=lower(a) if mode!='ch' else a;bb=lower(b) if mode!='cl' else b
        # In CH-only runs sweep CH exhaustively, retaining a varied CL.
        if mode=='ch':
            rr[1]=(rr[1]&0xffff0000)|(a<<8)|b;expected=rr.copy();aa=b;bb=lower(a)
        expected[1]=(rr[1]&0xffff0000)|(bb<<8)|aa
        v=a
        ff=flags(aa,bb) if mode=='pair' else flags(v,65) if v<65 else flags(v,90) if v>90 else flags(v,32,True)
        for r,value in zip(regs,rr):em.reg_write(r,value)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7 if cases%2 else 2)
        em.emu_start(start,end,count=11)
        require(em.reg_read(x.UC_X86_REG_EIP)==end,'wrong endpoint')
        require([em.reg_read(r) for r in regs]==expected,'register or preserved-bit mismatch')
        require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==ff,'modeled flags mismatch')
        cases+=1
    require(not writes and bytes(em.mem_read(0x41999,len(raw['fold'])))==raw['fold'],'unexpected write')
    return dict(cases=cases,individual_fold_cases=512,exhaustive_original_byte_pairs=65536,
      all_registers=True,modeled_flags=True,no_memory_writes=True,
      scope='Actual original CL/CH fold blocks and CMP for every byte pair. Does not execute the surrounding comparator loop or return.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted()
    scan=advance_evidence.previous.evidence.scan_data();side=advance_evidence.previous.side_data()
    advance=advance_evidence.advance_data();textures=texture_evidence.texture_data();wrapper=wrapper_evidence.wrapper_data()
    dash=dash_evidence.dash_data();table=previous.table_data();fold=fold_data()
    require(all(mp['exe_sha256']==p['exe_sha256'] for p in [profile,scan[3],side[2],advance[2],textures[2],wrapper[2],dash[2],table[2],fold[2]]),'executable mismatch')
    require(mp['wad_sha256']==scan[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-texture-fold';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan,side,advance,textures,wrapper,dash,table,fold))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalTextureFold'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=cross_check(fold[0]) if args.cross_check else None
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=combined_units(spec['units'],scan[1],side[1],advance[1],textures[1],wrapper[1],dash[1],table[1],fold[1]),
      cells=len(data['cells']),pinned_rows=475,reused_declarations=REUSED,cross_check=native,
      scope='Original ASCII folding blocks and byte comparison, exact registers, modeled flags and memory preservation. Opt-in interpreter preserves lifted old executions. Complete comparator, caller join, search loop and reachable startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original byte folding and comparison; isolated interpreter extension and inherited certificate.')
if __name__=='__main__':main()

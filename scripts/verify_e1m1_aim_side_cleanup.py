#!/usr/bin/env python3
"""Conditional owned/no-coalescing side cleanup, not initialized startup."""
import argparse, hashlib, json, re, struct, subprocess, sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_side_loop as previous
import verify_original_inline_thrust as extraction
ROOT,require=previous.ROOT,previous.require
MODULES=['E1M1AimSideStack','OriginalSideCleanup','E1M1AimSideCleanup']
NAMESPACE='Doom.Verification.ExtractedAimSideCleanup'
HEADER='open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimSideLoop E1M1AimSideStack\nopen Doom.Proofs.E1M1AimTextureCatalog (BodySafe)\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'

def inputs():
    e=previous.previous.previous.previous.previous.previous.previous
    data,mp=e.pinned_data();_,profile,raw=e.extracted()
    require(profile['exe_sha256']==mp['exe_sha256'],'inherited EXE mismatch')
    return data,profile,raw

def cleanup_data(spec=None):
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    if spec is None:spec=json.loads((ROOT/'tests/reference/original-side-cleanup.json').read_text())
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    return raw,spec['units'],profile

def contracts():
    return [(m,n) for m in MODULES for n in re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M)]

def contract(module,name):return previous.contract(module,name)

def names():
    return [NAMESPACE+'.'+n+'_checked' for n in ['cleanup','free','cleanupProgram','program']]+[
      full for m,n in contracts() for full in [NAMESPACE+'.'+m+'.'+n+'_checked','Doom.Proofs.'+m+'.'+n]]

def certificate(data,raw):
    bs,_,_=cleanup_data()
    source='import Doom.Proofs.E1M1AimSideCleanup\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for name,blob in bs.items():
        source+='def '+name+' : List UInt8 := ['+','.join(hex(b) for b in blob)+']\n'
        source+='theorem '+name+'_checked : '+name+'=Doom.Proofs.OriginalSideCleanup.'+name+'Bytes := by decide +kernel\n'
    source+='def cleanupProgram := OriginalSideCleanup.bytesProgram cleanup free\n'
    source+='theorem cleanupProgram_checked : cleanupProgram=OriginalSideCleanup.program := by rw [cleanupProgram,cleanup_checked,free_checked]; rfl\n'
    source+='def program : X86ByteRoutine.Program := fun pc => match Doom.Verification.ExtractedAimTextureLookup.iterationProgram pc with\n  | some op => some op\n  | none => X86ByteRoutine.liftProgram cleanupProgram pc\n'
    source+='theorem program_checked : program=E1M1AimSideCleanup.program := by unfold program; rw [Doom.Verification.ExtractedAimTextureLookup.iterationProgram_checked,cleanupProgram_checked]; rfl\n'
    for module,name in contracts():
        decl,args=contract(module,name)
        decl=decl.replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('Doom.Proofs.OriginalSideCleanup.program',NAMESPACE+'.cleanupProgram').replace('Doom.Proofs.E1M1AimSideCleanup.program',NAMESPACE+'.program')
        source+='namespace '+module+'\n'+changed+' := by\n'
        rewrites=[NAMESPACE+'.'+n+'_checked' for n in ['cleanupProgram','program'] if NAMESPACE+'.'+n in changed]
        if changed!=decl:source+='  simp only ['+','.join(rewrites)+']\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing cleanup audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        m=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+full)
        require({a.strip() for a in (m[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check_loop_cleanup():
    """Independent uninterrupted loop + real free + caller RET, constructed image."""
    import capstone, unicorn as u
    from unicorn import x86_const as x
    table,queries,fields,metadata=previous.previous.pinned_data()
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/sw['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest()==sw['wad_sha256'],'WAD pin mismatch')
    n,directory=struct.unpack_from('<II',wad,4)
    lumps=[struct.unpack_from('<II8s',wad,directory+16*i) for i in range(n)]
    marker=next(i for i,(_,_,name) in enumerate(lumps) if name.rstrip(b'\0')==b'E1M1')
    p,size,_=lumps[marker+3];sides=wad[p:p+size]
    require(hashlib.sha256(sides).hexdigest()==metadata['lump_sha256']['E1M1_SIDEDEFS'],'side hash mismatch')
    search=previous.previous.previous.previous; caller=previous.previous.previous.caller
    dash=search.table_evidence.previous.dash_data()[0]
    tbl=search.table_evidence.table_data()[0]
    wrapper=search.table_evidence.wrapper_evidence.wrapper_data()[0]
    cmp=search.previous.previous.iteration_data()[0]
    adv=caller.previous.advance_data()[0];side=caller.previous.previous.side_data()[0]
    ranges=[(0x346f0,dash['entry'],10),(0x34700,tbl['table'],10),
      (0x34722,search.search_data()[0]['continuation'],14),(0x3473c,tbl['missing'],1),
      (0x34741,dash['restore'],6),(0x34750,wrapper['wrapper'],15),
      (0x4198c,cmp['entry']+search.previous.previous.previous.fold_data()[0]['fold']+cmp['suffix'],33),
      (0x2e47e,caller.texture_data()[0]['textures'],14),(0x2e4af,side['link'],11),
      (0x2e4d1,adv['latch'],4),(0x2e46a,adv['offsets'],7)]
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
    for page in [0x2c000,0x2e000,0x30000,0x34000,0x41000]:em.mem_map(page,4096)
    em.mem_map(0x600000,0x30000)
    em.mem_map(0x630000,4096)
    em.mem_map(0x39000,4096)
    cleanup=cleanup_data()[0]
    em.mem_write(0x2e4dd,cleanup["cleanup"]);em.mem_write(0x39600,cleanup["free"])
    for pc,data,count in ranges:
        listing=list(dec.disasm(data,pc))
        require(len(listing)==count and b''.join(bytes(i.bytes) for i in listing)==data,'independent decoding mismatch')
        em.mem_write(pc,data)
    source,dest,base,sp=0x610000,0x620000,0x700000,0x600f00
    block,user,prev,nxt,stop=source-24,0x600800,0x60ff00,0x615000,0x630100
    saved=[0x12345678,0x87654321,0xabcd1234,0x11223344,0x55667788,0x99aabbcc]
    word=lambda v:struct.pack('<I',v&0xffffffff)
    for a,v in [(block,nxt-block),(block+4,user),(block+8,1),(block+12,0x1d4a11),
      (block+16,nxt),(block+20,prev),(prev,block-prev),(prev+4,1),(prev+16,block),
      (nxt+4,1),(nxt+20,block),(user,source),(sp+4,source),(sp+32,stop)]:em.mem_write(a,word(v))
    for i,v in enumerate(saved):em.mem_write(sp+8+4*i,word(v))
    upper=bytes(em.mem_read(sp+4,32))
    em.mem_write(source,sides);em.mem_write(dest,b'\xa5'*(18*648))
    em.mem_write(0x300e0,word(0x601000));em.mem_write(0x300e4,word(125))
    em.mem_write(0x2c148,word(base));em.mem_write(0x2c11c,word(648));em.mem_write(0x2c118,word(dest))
    for i,name in enumerate(table):
        em.mem_write(0x601000+4*i,word(0x602000+16*i));em.mem_write(0x602000+16*i,name)
    protected=[(source,len(sides)),(0x601000,4*125),(0x602000,16*125),
      (0x300e0,8),(0x2c148,4),(0x2c118,8)]
    before=[bytes(em.mem_read(a,n)) for a,n in protected]
    expected=bytearray();ids=[queries[q][1] for q in fields]
    for i in range(648):
        ox,oy=struct.unpack_from('<hh',sides,30*i)
        sector=struct.unpack_from('<h',sides,30*i+28)[0]
        expected+=word(ox<<16)+word(oy<<16)+struct.pack('<HHH',*ids[3*i:3*i+3])+word(base+86*sector)
    registers=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
      x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    for r,v in zip(registers,[0xdeadbeef,source+4,dest,source,sp,0,source+20,source+12]):em.reg_write(r,v)
    em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
    stats=dict(cleanup_instructions=0,instructions=0,sides=0,exact_return_ids=0,all_prior_records_at_every_header=True,source_catalog_globals_preserved=True,exact_registers_at_every_header=True,published_side_global_preserved=True,all_inputs_at_every_header=True)
    writes=[];expected_cleanup=[];cleanup_memory=[]
    em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&0xffffffff)))
    def trace(machine,address,_size,_data):
        if address==stop:machine.emu_stop();return
        if address==0x2e4dd:
            require(bytes(machine.mem_read(sp+4,32))==upper,'upper stack did not survive loop')
            require(bytes(machine.mem_read(dest,len(expected)))==bytes(expected),'loop output before cleanup')
            rr=[machine.reg_read(r) for r in registers]
            expected_cleanup.extend([(sp-4,4,0x2e4e6),(sp-8,4,rr[3]),(sp-12,4,rr[1]),(sp-16,4,rr[2]),
              (user,4,0),(block+4,4,0),(block+8,4,0),(block+12,4,0)])
            memory=bytearray(machine.mem_read(0x600000,0x30000))
            for a,n,v in expected_cleanup:memory[a-0x600000:a-0x600000+n]=word(v)
            cleanup_memory.append(bytes(memory));writes.clear()
        if expected_cleanup:stats['cleanup_instructions']+=1
        require(address!=0x34760,'unexpected I_Error arm')
        stats['instructions']+=1
        if address==0x2e46a:
            i=stats['sides'];require(i<648,'extra side body')
            expected_regs=[source+4+30*i,dest+18*i,source+30*i,sp,i,source+20+30*i,source+12+30*i]
            require([machine.reg_read(r) for r in registers[1:]]==expected_regs,'body header register invariant mismatch')
            require(all(bytes(machine.mem_read(a,n))==old for (a,n),old in zip(protected,before)),'body header input invariant mismatch')
            require(bytes(machine.mem_read(dest,18*i))==bytes(expected[:18*i]) if i else True,'earlier record changed')
            stats['sides']+=1
        if address in [0x2e483,0x2e494,0x2e4a5]:
            k=stats['exact_return_ids'];require(k<1944,'extra lookup return')
            require(machine.reg_read(x.UC_X86_REG_EAX)==ids[k],f'first-match ID mismatch at field {k}')
            stats['exact_return_ids']+=1
    em.hook_add(u.UC_HOOK_CODE,trace)
    em.emu_start(0x2e46a,0,count=10000000)
    require(em.reg_read(x.UC_X86_REG_EIP)==stop,'did not execute caller return')
    require(stats['sides']==648 and stats['exact_return_ids']==1944,'incomplete pinned side loop')
    require(bytes(em.mem_read(dest,len(expected)))==bytes(expected),'complete side output mismatch')
    require(all(bytes(em.mem_read(a,n))==old for (a,n),old in zip(protected,before)),'source/catalog/global mutation')
    final=[nxt,saved[4],saved[3],saved[5],sp+36,saved[0],saved[2],saved[1]]
    require([em.reg_read(r) for r in registers]==final,'final register mismatch')
    require(writes==expected_cleanup,'cleanup ordered writes mismatch')
    require(bytes(em.mem_read(0x600000,0x30000))==cleanup_memory[0],'cleanup full mapped memory mismatch')
    require(stats['cleanup_instructions']==33,'cleanup instruction count')
    return dict(**stats,complete_output_sha256=hashlib.sha256(expected).hexdigest(),all_final_registers=True,ordered_cleanup_writes=True,full_cleanup_memory=True,saved_stack=True,
      scope='Constructed source/catalog/owned heap fixture, continuous 648-body loop + selected owned no-coalescing cleanup and caller RET. Not reached startup. Final ADD ESP flags are forgotten in the Lean model and not claimed.')

def cross_check_local():
    """Sequential memory oracle; includes aliases excluded by Placement."""
    import random, capstone, unicorn as u
    from unicorn import x86_const as x
    raw=cleanup_data()[0];rng=random.Random(0x39600)
    dec=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_32)
    for name,pc in [('cleanup',0x2e4dd),('free',0x39600)]:
        listing=list(dec.disasm(raw[name],pc))
        require(b''.join(bytes(i.bytes) for i in listing)==raw[name],'incomplete CPU decode')
        # Full free includes unselected error/coalescing arms; selected path is 33 instructions.
    regs=[x.UC_X86_REG_EAX,x.UC_X86_REG_ECX,x.UC_X86_REG_EDX,x.UC_X86_REG_EBX,
      x.UC_X86_REG_ESP,x.UC_X86_REG_EBP,x.UC_X86_REG_ESI,x.UC_X86_REG_EDI]
    cases=0
    for i in range(128):
        em=u.Uc(u.UC_ARCH_X86,u.UC_MODE_32)
        for a in [0,0x2e000,0x39000,0x600000,0x630000]:em.mem_map(a,4096)
        em.mem_write(0x2e4dd,raw['cleanup']);em.mem_write(0x39600,raw['free'])
        memory={0:bytearray(rng.randbytes(4096)),0x600000:bytearray(rng.randbytes(4096))}
        def put(a,v):memory[a&~4095][a&4095:(a&4095)+4]=struct.pack('<I',v&0xffffffff)
        def get(a):return struct.unpack_from('<I',memory[a&~4095],a&4095)[0]
        sp=0x600c00+i%4;block=0x600400+i%4;prev,nxt=0x600300,0x600500
        user=[0x600800,sp+8,sp-8,257][i//32];stop=0x630100
        rr=[rng.getrandbits(32) for _ in regs];rr[4]=sp
        for a,v in [(sp+4,block+24),(sp+32,stop),(block+4,user),(block+8,1),
          (block+12,0x1d4a11),(block+16,nxt),(block+20,prev),(prev+4,1),(nxt+4,2)]:put(a,v)
        for a,bs in memory.items():em.mem_write(a,bytes(bs))
        for r,v in zip(regs,rr):em.reg_write(r,v)
        em.reg_write(x.UC_X86_REG_EFLAGS,0x8d7)
        expected=[]
        def store(a,v):expected.append((a,4,v&0xffffffff));put(a,v)
        for a,v in [(sp-4,0x2e4e6),(sp-8,rr[3]),(sp-12,rr[1]),(sp-16,rr[2]),
          (user,0),(block+4,0),(block+8,0),(block+12,0)]:store(a,v)
        final=[nxt,get(sp+24),get(sp+20),get(sp+28),sp+36,get(sp+8),get(sp+16),get(sp+12)]
        writes=[];visits=[];flag_checks=[]
        def cmp_flags(a,b):
            result=(a-b)&0xffffffff
            overflow=bool((a^b)&(a^result)&0x80000000)
            return ((result==0)<<6)|((result>>31)<<7)|(overflow<<11)|int(a<b)
        expected_flags={0x3961c:cmp_flags(0x1d4a11,0x1d4a11),0x39627:cmp_flags(user,256),
          0x39668:cmp_flags(1,0),0x3968c:cmp_flags(2,0),0x2e4e6:cmp_flags(2,0)}
        def trace(machine,address,_size,_data):
            if address==stop:machine.emu_stop();return
            visits.append(address)
            if address in expected_flags:
                require(machine.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==expected_flags[address],'modeled comparison flags mismatch')
                flag_checks.append(address)
        em.hook_add(u.UC_HOOK_MEM_WRITE,lambda _e,_a,a,n,v,_d:writes.append((a,n,v&0xffffffff)))
        em.hook_add(u.UC_HOOK_CODE,trace)
        em.emu_start(0x2e4dd,0,count=50)
        require(em.reg_read(x.UC_X86_REG_EIP)==stop and len(visits)==33,'cleanup return/count')
        require(len(flag_checks)==5,'missing flag observations')
        require([em.reg_read(r) for r in regs]==final,'cleanup registers')
        require(writes==expected,'cleanup ordered writes')
        require(all(bytes(em.mem_read(a,4096))==bs for a,bs in memory.items()),'cleanup mapped memory')
        cases+=1
    return dict(cases=cases,all_registers=True,ordered_writes=True,mapped_memory=True,modeled_comparison_flags=True,
      upper_saved_register_alias_cases=32,callee_saved_register_alias_cases=32,minimal_owned_pointer_cases=32,
      scope='Selected owned/no-coalescing branch only. Alias cases exercise OriginalSideCleanup ordering but are excluded by composite Placement. Final ADD ESP flags forgotten.')

def cross_check():
    return dict(local=cross_check_local(),loop=cross_check_loop_cleanup())

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,profile,raw=inputs();bs,units,cp=cleanup_data()
    require(profile['exe_sha256']==cp['exe_sha256'],'cleanup EXE mismatch')
    out=ROOT/'artifacts/e1m1-aim-side-cleanup';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build',*[f'Doom.Proofs.{m}' for m in MODULES]],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=cross_check();(out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-side-loop/report.json').read_text())
    combined=dict(prior['units']);combined.update({'cleanup_'+n:v for n,v in units.items()})
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=prior['wad_sha256'],units=combined,
      cells=prior['cells'],pinned_rows=prior['pinned_rows'],public_theorems=len(contracts()),
      audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),cross_check=native,
      scope='648-body loop through real owned/no-coalescing Z_Free and caller RET from one incoming source/catalog/heap image and static region separation. Restores six registers and caller PC, preserves all sector pointers. Initial valid owned block and busy neighbors are explicit assumptions, not proved DOS heap reachability. Loader entry, R_InitTextures and startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: conditional side loop/owned cleanup; cumulative byte/data certificate and strict audit.')
if __name__=='__main__':main()

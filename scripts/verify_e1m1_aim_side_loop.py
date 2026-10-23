#!/usr/bin/env python3
"""One-image complete side loop; not reachable startup or R_InitTextures."""
import argparse, hashlib, json, re, struct, subprocess, sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_texture_catalog as previous
ROOT, require = previous.ROOT, previous.require
MODULES=['E1M1AimSideLoop','E1M1AimPinnedSides']
NAMESPACE='Doom.Verification.ExtractedAimSideLoop'

def sector_data():
    profile=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/profile['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest()==profile['wad_sha256'],'WAD pin mismatch')
    n,directory=struct.unpack_from('<II',wad,4)
    lumps=[struct.unpack_from('<II8s',wad,directory+16*i) for i in range(n)]
    marker=next(i for i,(_,_,name) in enumerate(lumps) if name.rstrip(b'\0')==b'E1M1')
    p,size,label=lumps[marker+3]
    require(label.rstrip(b'\0')==b'SIDEDEFS' and size==30*648 and p+size<=len(wad),'bad raw-side mapping')
    sides=wad[p:p+size]
    require(hashlib.sha256(sides).hexdigest()==previous.pinned_data()[3]['lump_sha256']['E1M1_SIDEDEFS'],'raw-side hash mismatch')
    _,sector_size,sector_label=lumps[marker+8]
    require(sector_label.rstrip(b'\0')==b'SECTORS' and sector_size==85*26,'sector shape mismatch')
    indices=[struct.unpack_from('<H',sides,30*i+28)[0] for i in range(648)]
    require(all(i<85 for i in indices),'invalid pinned sector index')
    return indices,dict(wad_sha256=profile['wad_sha256'],sidedefs_sha256=hashlib.sha256(sides).hexdigest(),side_count=648,sector_count=85)

def literals(indices):
    return 'def sectorIndices : List (Fin 85) := [\n  '+',\n  '.join(','.join(map(str,indices[i:i+36])) for i in range(0,len(indices),36))+']\n'

def contracts():
    return [(m,n) for m in MODULES for n in re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M)]

def contract(module,name):
    # Qualify own definitions, preserving complete theorem signatures.
    return previous.contract(module,name)

def names():
    return [NAMESPACE+'.sectorIndices_checked']+[
        full for m,n in contracts() for full in [NAMESPACE+'.'+m+'.'+n+'_checked','Doom.Proofs.'+m+'.'+n]]

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimPinnedSides\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+previous.previous.previous.table_evidence.HEADER
    source+='open Doom.Proofs.E1M1AimTextureCatalog Doom.Proofs.E1M1AimPinnedCatalog Doom.Proofs.E1M1AimSideLoop Doom.Proofs.E1M1AimPinnedSides\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
    source+=literals(sector_data()[0])
    source+='theorem sectorIndices_checked : sectorIndices=Doom.Proofs.E1M1AimPinnedSides.sectorIndices := by decide +kernel\n'
    for module,name in contracts():
        decl,args=contract(module,name)
        decl=decl.replace('theorem '+name,'theorem '+name+'_checked',1)
        changed=decl.replace('E1M1AimSideLookup.iterationProgram','Doom.Verification.ExtractedAimTextureLookup.iterationProgram')
        source+='namespace '+module+'\n'+changed+' := by\n'
        if changed!=decl:source+='  rw [Doom.Verification.ExtractedAimTextureLookup.iterationProgram_checked]\n'
        source+='  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'";require(marker in output,'missing one-image side-loop audit')
    inherited,rest=output.split(marker,1);previous.audit(inherited);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check_loop():
    """Empirical entire 648-body loop on a constructed, not initialized, image."""
    import capstone, unicorn as u
    from unicorn import x86_const as x
    table,queries,fields,metadata=previous.pinned_data()
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/sw['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest()==sw['wad_sha256'],'WAD pin mismatch')
    n,directory=struct.unpack_from('<II',wad,4)
    lumps=[struct.unpack_from('<II8s',wad,directory+16*i) for i in range(n)]
    marker=next(i for i,(_,_,name) in enumerate(lumps) if name.rstrip(b'\0')==b'E1M1')
    p,size,_=lumps[marker+3];sides=wad[p:p+size]
    require(hashlib.sha256(sides).hexdigest()==metadata['lump_sha256']['E1M1_SIDEDEFS'],'side hash mismatch')
    search=previous.previous.previous; caller=previous.previous.caller
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
    for pc,data,count in ranges:
        listing=list(dec.disasm(data,pc))
        require(len(listing)==count and b''.join(bytes(i.bytes) for i in listing)==data,'independent decoding mismatch')
        em.mem_write(pc,data)
    source,dest,base,sp=0x610000,0x620000,0x700000,0x600f00
    word=lambda v:struct.pack('<I',v&0xffffffff)
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
    stats=dict(instructions=0,sides=0,exact_return_ids=0,all_prior_records_at_every_header=True,source_catalog_globals_preserved=True,exact_registers_at_every_header=True,published_side_global_preserved=True,all_inputs_at_every_header=True)
    def trace(machine,address,_size,_data):
        if address==0x2e4dd:machine.emu_stop();return
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
    require(em.reg_read(x.UC_X86_REG_EIP)==0x2e4dd,'did not reach cleanup boundary')
    require(stats['sides']==648 and stats['exact_return_ids']==1944,'incomplete pinned side loop')
    require(bytes(em.mem_read(dest,len(expected)))==bytes(expected),'complete side output mismatch')
    require(all(bytes(em.mem_read(a,n))==old for (a,n),old in zip(protected,before)),'source/catalog/global mutation')
    final=[648,source+4+30*648,dest+18*648,source+30*648,sp,648,source+20+30*648,source+12+30*648]
    require([em.reg_read(r) for r in registers]==final,'final register mismatch')
    require(em.reg_read(x.UC_X86_REG_EFLAGS)&0x8c1==0x40,'final modeled flags mismatch')
    return dict(**stats,complete_output_sha256=hashlib.sha256(expected).hexdigest(),all_final_registers=True,
      scope='Empirical full pinned loop from 0x2e46a to cleanup boundary 0x2e4dd on constructed catalog/source/placement. CPU evidence is empirical; the separate one-image Lean loop theorem is universal under its explicit image/layout assumptions. Not DOS initialization or cleanup execution.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cross-check',action='store_true');args=ap.parse_args()
    data,mp=previous.previous.previous.previous.previous.previous.pinned_data()
    _,profile,raw=previous.previous.previous.previous.previous.previous.extracted()
    out=ROOT/'artifacts/e1m1-aim-side-loop';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build',*[f'Doom.Proofs.{m}' for m in MODULES]],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=dict(pinned_loop=cross_check_loop(),inherited_lookup_checks=previous.previous.cross_check())
        (out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-texture-catalog/report.json').read_text())
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=prior['units'],cells=len(data['cells']),pinned_rows=prior['pinned_rows'],
        audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),public_theorems=len(contracts()),cross_check=native,raw_sides=sector_data()[1],
        scope='Full 648-body byte-prefix loop from one incoming image and regional storage layout. All body successes, guards, stable count, future inputs and earlier pointers derived. Conditional catalog/source image and storage remain; no entry, allocation, cleanup execution or initialized startup claim.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: one-image full pinned side loop; strict cumulative byte/data certificate.')

if __name__=='__main__':main()

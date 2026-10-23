#!/usr/bin/env python3
"""Conditional stable-catalog proofs; no DOS catalog initialization claim."""
import argparse, hashlib, json, re, struct, subprocess, sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import verify_e1m1_aim_texture_lookup as previous
ROOT, require = previous.ROOT, previous.require

def pinned_data():
    table, mapping, report = previous.catalog_data()
    profile=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/profile['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest()==profile['wad_sha256'],'WAD pin mismatch')
    n, directory=struct.unpack_from('<II',wad,4)
    lumps=[struct.unpack_from('<II8s',wad,directory+16*i) for i in range(n)]
    marker=next(i for i,(_,_,name) in enumerate(lumps) if name.rstrip(b'\0')==b'E1M1')
    p,size,label=lumps[marker+3]
    require(label.rstrip(b'\0')==b'SIDEDEFS' and size==648*30,'pinned side shape mismatch')
    sides=wad[p:p+size]
    require(hashlib.sha256(sides).hexdigest()==report['lump_sha256']['E1M1_SIDEDEFS'],'side extraction mismatch')
    queries=list(mapping)
    fields=[queries.index(sides[i+off:i+off+8]) for i in range(0,size,30) for off in [4,12,20]]
    require(len(table)==125 and len(queries)==33 and len(fields)==1944,'pinned catalog dimensions changed')
    return table,[(q,mapping[q]) for q in queries],fields,report

def literals(table,queries,fields):
    byte_list=lambda b:'['+','.join(str(v) for v in b)+']'
    return ('def textureBytes : List (List (BitVec 8)) := [\n  '+',\n  '.join(map(byte_list,table))+']\n'
      +'def queryBytes : List (List (BitVec 8) × Nat) := [\n  '+',\n  '.join('('+byte_list(q)+','+str(j)+')' for q,j in queries)+']\n'
      +'def fieldNames : List (Fin 33) := [\n  '+',\n  '.join(','.join(map(str,fields[i:i+54])) for i in range(0,len(fields),54))+']\n')

def pinned_source():
    table,queries,fields,_=pinned_data()
    return '''import Doom.Proofs.E1M1AimTextureCatalog
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
namespace Doom.Proofs.E1M1AimPinnedCatalog
open Verification X86 X86Memory X86Control BlockSummary E1M1AimTextureCatalog
-- Extracted name metadata only. Authenticated afresh by the cumulative certificate.
-- No pointer placement or DOS R_InitTextures construction is supplied here.
'''+literals(table,queries,fields)+'''
def nameOf (bytes : List (BitVec 8)) : Name := fun j => bytes[j]?.getD 0
def textureName (i : Nat) : Name := nameOf (textureBytes[i]?.getD [])
def queryName (q : Fin 33) : Name := nameOf ((queryBytes[q.val]?.getD ([],0)).1)
def textureID (q : Fin 33) : Nat := (queryBytes[q.val]?.getD ([],0)).2
def fieldQuery (side : Fin 648) (field : Fin 3) : Fin 33 :=
  fieldNames[3*side.val+field.val]?.getD 0

def catalog (table : Word) (pointer : Nat → Word) (query : Word) (q : Fin 33) : Catalog :=
  ⟨125,table,pointer,textureName,query,queryName q⟩

theorem dimensions : textureBytes.length=125 ∧ queryBytes.length=33 ∧ fieldNames.length=1944 := by decide +kernel

/-- All finite first-match obligations, including every earlier nonmatch, are
kernel checked using the proved comparator's ASCII-folded eight-byte spec. -/
theorem finite_results : ∀ q : Fin 33,
    (queryName q 0=0x2d ∧ textureID q=0) ∨
    (queryName q 0≠0x2d ∧ textureID q<125 ∧
      compareName 8 (textureName (textureID q)) (queryName q)=0 ∧
      ∀ i : Fin (textureID q), compareName 8 (textureName i.val) (queryName q)≠0) := by
  decide +kernel

theorem pinned_resolved (table query : Word) (pointer : Nat → Word) (q : Fin 33) :
    Resolved (catalog table pointer query q) (textureID q) := by
  rcases finite_results q with dash|⟨named,bound,equal,earlier⟩
  · exact Or.inl dash
  · exact Or.inr ⟨named,by refine ⟨by change 125≤2147483647; decide,bound,equal,?_⟩; intro i hi; exact earlier ⟨i,hi⟩⟩

theorem pinned_call (s : X86Memory.State) (f : Option Flags) (dest table query : Word)
    (pointer : Nat → Word) (q : Fin 33)
    (image : Image (catalog table pointer query q) s.memory)
    (safe : CallSafe (catalog table pointer query q) (s.regs 4))
    (name : s.regs 0=query) :
    (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).pc=dest.toNat ∧
      (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).core.regs 0=BitVec.ofNat 32 (textureID q) := by
  exact call_result _ s f dest _ image safe name (pinned_resolved table query pointer q)

theorem pinned_side_returned (s : X86Memory.State) (f : Option Flags) (table : Word)
    (pointer : Nat → Word) (side : Fin 648)
    (images : ∀ k : Fin 3, Image (catalog table pointer (s.regs (if k=0 then 0 else if k=1 then 7 else 6)) (fieldQuery side k)) s.memory)
    (safe : ∀ k : Fin 3, SideSafe (catalog table pointer (s.regs (if k=0 then 0 else if k=1 then 7 else 6)) (fieldQuery side k)) s) :
    E1M1AimSideLookup.Returned s f := by
  apply side_returned (catalog table pointer (s.regs 0) (fieldQuery side 0))
    (catalog table pointer (s.regs 7) (fieldQuery side 1))
    (catalog table pointer (s.regs 6) (fieldQuery side 2)) s f
    (textureID (fieldQuery side 0)) (textureID (fieldQuery side 1)) (textureID (fieldQuery side 2))
  exact ⟨⟨images 0,images 1,images 2⟩,⟨safe 0,safe 1,safe 2⟩,⟨rfl,rfl,rfl⟩,
    ⟨pinned_resolved _ _ _ _,pinned_resolved _ _ _ _,pinned_resolved _ _ _ _⟩⟩
/-- Incoming body-entry catalog images and explicit write separation only.
No assumed Returned, reached post-call image or helper execution. -/
def bodyCatalog (s : X86Memory.State) (table : Word) (pointer : Nat → Word)
    (row : Fin 648) (k : Fin 3) : Catalog :=
  catalog table pointer (s.regs (if k=0 then 1 else if k=1 then 7 else 6)) (fieldQuery row k)
structure BodyReady (s : X86Memory.State) (table : Word) (pointer : Nat → Word) (row : Fin 648) : Prop where
  images : ∀ k : Fin 3, Image (bodyCatalog s table pointer row k) s.memory
  safe : ∀ k : Fin 3, SideSafe (bodyCatalog s table pointer row k) s
  offsets : ∀ k : Fin 3, ∀ p, Reads (bodyCatalog s table pointer row k) p → OffsetSafe s p

theorem pinned_body_catalog (s : X86Memory.State) (table : Word) (pointer : Nat → Word)
    (row : Fin 648) (ready : BodyReady s table pointer row) :
    BodyCatalog (bodyCatalog s table pointer row 0) (bodyCatalog s table pointer row 1)
      (bodyCatalog s table pointer row 2) s
      (textureID (fieldQuery row 0)) (textureID (fieldQuery row 1)) (textureID (fieldQuery row 2)) := by
  refine ⟨⟨⟨ready.images 0,ready.images 1,ready.images 2⟩,?_,⟨rfl,rfl,rfl⟩,
    ⟨pinned_resolved _ _ _ _,pinned_resolved _ _ _ _,pinned_resolved _ _ _ _⟩⟩,?_⟩
  · exact ⟨side_safe_transport _ _ _ (ready.safe 0) rfl rfl,
      side_safe_transport _ _ _ (ready.safe 1) rfl rfl,
      side_safe_transport _ _ _ (ready.safe 2) rfl rfl⟩
  · intro d hd p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl
    · exact ready.offsets 0 p hp
    · exact ready.offsets 1 p hp
    · exact ready.offsets 2 p hp

theorem pinned_body (s : X86Memory.State) (f : Option Flags) (table : Word) (pointer : Nat → Word)
    (row : Fin 648) (ready : BodyReady s table pointer row)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : BodySafe s (s.regs 3+28)) (sectorSafe : BodySafe s 0x2c148) :
    (∃ k≤3*(202*2147483647+30)+36,
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k ⟨s,f,0x2e46a⟩ (body s)) ∧
    E1M1NoiseImage.Realizes
      (E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress sideBase side) (E1M1AimSideEncoding.sectorAddress sectorBase index))
      (body s).core.memory := by
  exact ⟨body_execution s f,body_emitted _ _ _ s _ _ _ (pinned_body_catalog s table pointer row ready)
    side index sideBase sectorBase input sourceSafe sectorSafe⟩
end Doom.Proofs.E1M1AimPinnedCatalog
'''

NAMESPACE='Doom.Verification.ExtractedAimTextureCatalog'
MODULES=['E1M1AimTextureCatalog','E1M1AimPinnedCatalog']

def contracts():
    return [(m,n) for m in MODULES for n in re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{m}.lean').read_text(),re.M)]

def contract(module,name):
    decl=previous.declaration(module,name)
    # Extract only top-level explicit binders, never identifiers in their types.
    rest=decl[len('theorem '+name):]; args=[]; depth=0; start=None
    for i,ch in enumerate(rest):
        if ch==':' and depth==0:break
        if ch=='(':
            if depth==0:start=i+1
            depth+=1
        elif ch==')':
            depth-=1
            if depth==0:args.extend(rest[start:i].split(':',1)[0].split())
    return decl,' '.join(args)

def names():
    return [NAMESPACE+'.'+n+'_checked' for n in ['textureBytes','queryBytes','fieldNames']]+[
      full for m,n in contracts() for full in [NAMESPACE+'.'+m+'.'+n+'_checked','Doom.Proofs.'+m+'.'+n]]

def certificate(data,raw):
    table,queries,fields,_=pinned_data()
    source='import Doom.Proofs.E1M1AimPinnedCatalog\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+previous.previous.table_evidence.HEADER
    source+='open Doom.Proofs.E1M1AimTextureCatalog Doom.Proofs.E1M1AimPinnedCatalog\n'
    source+=literals(table,queries,fields)
    for n in ['textureBytes','queryBytes','fieldNames']:
        source+='theorem '+n+'_checked : '+n+'=Doom.Proofs.E1M1AimPinnedCatalog.'+n+' := by decide +kernel\n'
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
    marker="'"+names()[0]+"'"; require(marker in output,'missing stable-catalog audit')
    inherited,rest=output.split(marker,1); previous.audit(inherited); rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check_pinned_loop():
    """Empirical entire 648-body loop on a constructed, not initialized, image."""
    import capstone, unicorn as u
    from unicorn import x86_const as x
    table,queries,fields,metadata=pinned_data()
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/sw['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest()==sw['wad_sha256'],'WAD pin mismatch')
    n,directory=struct.unpack_from('<II',wad,4)
    lumps=[struct.unpack_from('<II8s',wad,directory+16*i) for i in range(n)]
    marker=next(i for i,(_,_,name) in enumerate(lumps) if name.rstrip(b'\0')==b'E1M1')
    p,size,_=lumps[marker+3];sides=wad[p:p+size]
    require(hashlib.sha256(sides).hexdigest()==metadata['lump_sha256']['E1M1_SIDEDEFS'],'side hash mismatch')
    search=previous.previous; caller=previous.caller
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
    em.mem_write(0x2c148,word(base));em.mem_write(0x2c11c,word(648))
    for i,name in enumerate(table):
        em.mem_write(0x601000+4*i,word(0x602000+16*i));em.mem_write(0x602000+16*i,name)
    protected=[(source,len(sides)),(0x601000,4*125),(0x602000,16*125),
      (0x300e0,8),(0x2c148,4),(0x2c11c,4)]
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
    stats=dict(instructions=0,sides=0,exact_return_ids=0,all_prior_records_at_every_header=True,source_catalog_globals_preserved=True)
    def trace(machine,address,_size,_data):
        if address==0x2e4dd:machine.emu_stop();return
        require(address!=0x34760,'unexpected I_Error arm')
        stats['instructions']+=1
        if address==0x2e46a:
            i=stats['sides'];require(i<648,'extra side body')
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
      scope='Empirical full pinned loop from 0x2e46a to cleanup boundary 0x2e4dd on constructed catalog/source/placement. Not DOS initialization, cleanup execution, or a universal loop theorem.')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-module',action='store_true')
    ap.add_argument('--cross-check',action='store_true')
    args=ap.parse_args()
    if args.write_module:
        path=ROOT/'Doom/Proofs/E1M1AimPinnedCatalog.lean'
        require(not path.exists(),'refusing to overwrite existing module')
        path.write_text(pinned_source()); print(path); return
    data,mp=previous.previous.previous.previous.previous.pinned_data()
    _,profile,raw=previous.previous.previous.previous.previous.extracted()
    out=ROOT/'artifacts/e1m1-aim-texture-catalog';out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build',*[f'Doom.Proofs.{m}' for m in MODULES]],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(out/'Checked.lean')],cwd=ROOT,capture_output=True,text=True,timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout);require(not checked.stderr.strip(),'unexpected stderr')
    native=None
    if args.cross_check:
        native=dict(pinned_loop=cross_check_pinned_loop(),inherited_lookup_checks=previous.cross_check())
        (out/'cross-check.json').write_text(json.dumps(native,indent=2)+'\n')
    elif (out/'cross-check.json').exists():native=json.loads((out/'cross-check.json').read_text())
    prior=json.loads((ROOT/'artifacts/e1m1-aim-texture-lookup/report.json').read_text())
    report=dict(exe_sha256=profile['exe_sha256'],wad_sha256=mp['wad_sha256'],units=prior['units'],cells=len(data['cells']),pinned_rows=prior['pinned_rows'],
      audited_declarations=len(re.findall(r"^'",checked.stdout,re.M)),public_theorems=len(contracts()),cross_check=native,
      catalog=pinned_data()[3],scope='Conditional stable catalog, exact first matches, derived three-call success, body-entry source bridge and all protected-word frames. Catalog initialization, reachable separation, repetition, loader entry/cleanup and startup remain open.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: stable catalog first matches and derived side-body success; strict cumulative audit.')

if __name__=='__main__':main()

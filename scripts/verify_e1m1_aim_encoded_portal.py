#!/usr/bin/env python3
"""Bind encoded portal initialization to the authenticated E1M1 records."""
import argparse,json,re,subprocess
import verify_e1m1_aim_raw_portal as previous
import verify_e1m1_aim_loaded_scan as evidence
import hashlib,struct
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimEncodedPortal': ['geometry_source', 'side_source', 'flag_byte', 'sector_values', 'images', 'execution']}
CONTRACTS=[('E1M1AimEncodedPortal', 'geometry_source', 'r raw base m global rawImage vertices'), ('E1M1AimEncodedPortal', 'side_source', 'r raw base sector m front global rawImage sideImage'), ('E1M1AimEncodedPortal', 'flag_byte', 'r raw m image'), ('E1M1AimEncodedPortal', 'sector_values', 'r sector m present image'), ('E1M1AimEncodedPortal', 'images', 'total rows raw vertexBase sideBase sector m encoded fronts'), ('E1M1AimEncodedPortal', 'execution', 'total rows sector raw sideBase vertexBase base sp stack s f i hit loop ready verticesSafe good sidesSafe encoded fronts layout front back reserve present kind flagSourceSafe two')]
REUSED=['Doom.Proofs.E1M1NoiseImage.read_half','Doom.Proofs.E1M1NoiseImage.read_word']
PINNED=['row_count','rows_good','rows_front','rows_back','geometry_checked','records_good','records_front','records_back','pinned_execution']
NAMESPACE='Doom.Verification.ExtractedAimEncodedPortal'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Row': 'E1M1AimEncodedPortal', 'sides': 'E1M1AimEncodedPortal', 'portal': 'E1M1AimEncodedPortal', 'rawBytes': 'E1M1AimEncodedPortal', 'vertexBytes': 'E1M1AimEncodedPortal', 'sideBytes': 'E1M1AimEncodedPortal', 'sectorBytes': 'E1M1AimEncodedPortal', 'Encoded': 'E1M1AimEncodedPortal', 'Region': 'E1M1NoiseAllocation', 'cursor': 'E1M1LineScan', 'states': 'E1M1LineScan', 'Realizes': 'E1M1NoiseImage'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def names():
    return ([NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+
      ['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED+[NAMESPACE+"."+n for n in PINNED])

def certificate(data,raw,scan_inputs=None):
    source='import Doom.Proofs.E1M1AimEncodedPortal\n'+previous.certificate(data,raw,scan_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        source+='namespace '+module+'\n'+decl+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+=pinned_certificate(pinned_rows(scan_inputs)[0])
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'"
    require(marker in output,'missing initial portal audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def pinned_rows(scan_inputs=None):
    if scan_inputs is None:scan_inputs=evidence.scan_data()
    data,profile=scan_inputs[2],scan_inputs[3]
    share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/share['local_directory']/'doom1.wad').read_bytes()
    require(hashlib.sha256(wad).hexdigest()==profile['wad_sha256']==share['wad_sha256'],'pinned WAD hash mismatch')
    evidence.scan.iteration.setup.geometry.topology.decode_wad(wad)
    count,directory=struct.unpack_from('<II',wad,4)
    lumps=[]
    for i in range(count):
        start,size,name=struct.unpack_from('<II8s',wad,directory+16*i)
        lumps.append((name.rstrip(b'\0').decode('ascii'),wad[start:start+size]))
    start=next(i for i,(n,_) in enumerate(lumps) if n=='E1M1')
    source=dict(lumps[start+1:start+11])
    heights=[tuple((v<<16)&0xffffffff for v in struct.unpack_from('<hh',source['SECTORS'],off))
             for off in range(0,len(source['SECTORS']),26)]
    raw=list(struct.iter_unpack('<7H',source['LINEDEFS']))
    require(len(raw)==len(data['geometry'])==len(data['lines'])==475,'line count mismatch')
    rows=[]
    for i,(line,g,t) in enumerate(zip(raw,data['geometry'],data['lines'])):
        a,b,flags,_,_,fi,bi=line;index,low,tf,tb,fs,bs=t
        require((a,b)==tuple(g[:2]) and (i,flags&255,fi,bi)==(index,low,tf,tb),'record provenance mismatch')
        ff,fc=heights[fs];bf,bc=(0,0) if bi==65535 else heights[bs]
        rows.append([list(g),flags,fi,bi,fs,bs,ff,fc,bf,bc])
    return rows,dict(wad_sha256=profile['wad_sha256'],lines=475,sectors=len(heights),
      lump_sha256={k:hashlib.sha256(source[k]).hexdigest() for k in ['LINEDEFS','VERTEXES','SIDEDEFS','SECTORS']},
      parser_boundary='Python decoding plus SHA256 binds literals to WAD bytes; Lean checks finite facts and the memory-representation implication. No formal WAD parser or DOS startup refinement.')

def pinned_certificate(rows):
    source='open E1M1AimEncodedPortal\nset_option backward.isDefEq.respectTransparency false\nset_option maxHeartbeats 2000000\n'
    source+='def rows : List Row := ['+','.join('⟨⟨'+','.join(map(str,r[0]))+'⟩,'+','.join(map(str,r[1:]))+'⟩' for r in rows)+']\n'
    source+='''theorem row_count : rows.length=475 := by decide +kernel
 theorem rows_good : rows.all (fun r => E1M1LineSource.good r.geometry)=true := by decide +kernel
 theorem rows_front : rows.all (fun r => r.frontIndex != 65535)=true := by decide +kernel
 theorem rows_back : rows.all (fun r => r.flags.extractLsb' 0 8 &&& (4#8)==0 || r.backIndex != 65535)=true := by decide +kernel
 theorem geometry_checked : rows.map (fun r => (r.geometry.x2-r.geometry.x1,r.geometry.y2-r.geometry.y1))=
     Doom.Verification.ExtractedLineIteration.deltas := by decide +kernel
 def records (i : Fin 475) : Row := rows.get ⟨i.val,by simpa only [row_count] using i.isLt⟩
 theorem records_good (i : Fin 475) : E1M1LineSource.good (records i).geometry=true :=
   List.all_eq_true.mp rows_good _ (List.get_mem rows ⟨i.val,by simpa only [row_count] using i.isLt⟩)
 theorem records_front (i : Fin 475) : (records i).frontIndex≠65535 := by
   have h := List.all_eq_true.mp rows_front _ (List.get_mem rows ⟨i.val,by simpa only [row_count] using i.isLt⟩)
   simp only [bne_iff_ne] at h
   exact h
 theorem records_back (i : Fin 475) (two : (records i).flags.extractLsb' 0 8 &&& (4#8)≠0) :
     (records i).backIndex≠65535 := by
   have h := List.all_eq_true.mp rows_back _ (List.get_mem rows ⟨i.val,by simpa only [row_count] using i.isLt⟩)
   change ((records i).flags.extractLsb' 0 8 &&& (4#8)==0 || (records i).backIndex != 65535)=true at h
   simp only [Bool.or_eq_true,beq_iff_eq,bne_iff_ne] at h
   exact h.elim (fun zero => False.elim (two zero)) id
'''
    decl=declaration('E1M1AimEncodedPortal','execution')
    decl=decl.replace('theorem execution (total : Nat) (rows : Fin total → Doom.Proofs.E1M1AimEncodedPortal.Row)', 'theorem pinned_execution')
    decl=re.sub(r'\btotal\b','475',decl);decl=re.sub(r'\brows\b','records',decl)
    decl=decl.replace('    (good : ∀ j, E1M1LineSource.good (records j).geometry=true)\n','')
    decl=decl.replace('    (fronts : ∀ j, (records j).frontIndex≠65535)\n','')
    decl=decl.replace('    (present : (records i).backIndex≠65535) (kind : hit.isLine=true)','    (kind : hit.isLine=true)')
    decl=decl.replace('E1M1LineIteration.program','Doom.Verification.ExtractedLineIteration.program')
    source+=decl+' := by\n  unfold Doom.Verification.ExtractedLineIteration.program\n'
    source+='  rw ['+','.join('Doom.Verification.ExtractedLineIteration.'+n+'_checked' for n in evidence.scan.iteration.UNITS)+']\n'
    source+='''  exact E1M1AimEncodedPortal.execution 475 records sector raw sideBase vertexBase base sp stack s f i hit
    loop ready verticesSafe records_good sidesSafe encoded records_front layout front back reserve
    (records_back i two) kind flagSourceSafe two
'''
    return source

def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();scan_inputs=evidence.scan_data()
    rows,row_meta=pinned_rows(scan_inputs)
    require(mp['exe_sha256']==profile['exe_sha256']==scan_inputs[3]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan_inputs[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-encoded-portal';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan_inputs))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimEncodedPortal'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],
      units=evidence.combined_units(spec['units'],scan_inputs[1]),cells=len(data['cells']),
      reused_declarations=REUSED,pinned_rows=len(rows),map_encoding=row_meta,
      scope='Byte-level initial raw-line, decoded-vertex, side-pointer and sector-height representation derives all initial portal contents. Authenticated 475-row E1M1 specialization discharges geometry safety, front presence and back presence for two-sided lines. Encoding and storage remain initial-state premises; actual DOS startup construction is not proved. No new binary ranges, runtime, decoder or instruction semantics.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: authenticated E1M1 rows joined through byte encoding to complete portal scan; strict inherited audit.')
if __name__=='__main__':main()

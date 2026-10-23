#!/usr/bin/env python3
"""Certify compatible instruction-map union and continuous aiming-query execution."""
import argparse,json,re,subprocess
import verify_e1m1_aim_query_caller as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimProgramLink':['region_'+str(i) for i in range(137)]+['outside','compatible','contains_return','contains_query','append'],
 'E1M1AimLinkedQuery':['execution']}
QUERY_ARGS=previous.QUERY_ARGS
CONTRACTS=[
 ('E1M1AimProgramLink','compatible','pc'),
 ('E1M1AimProgramLink','contains_return','pc present'),
 ('E1M1AimProgramLink','contains_query','pc present'),
 ('E1M1AimProgramLink','append','cm exits n m start middle finish query returned'),
 ('E1M1AimLinkedQuery','execution',QUERY_ARGS+' scene shooter thing distance portals walls who initial')]
NAMESPACE='Doom.Verification.ExtractedAimLinkedQuery'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'CompatibleAt':'E1M1AimProgramLink','program':'E1M1AimProgramLink',
      'Initial':'E1M1AimQueryCaller','Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimLinkedQuery\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked : X86ReturnCleanup.Program := fun pc =>',
      '  match Doom.Verification.ExtractedAimCompletedReturn.linked pc with',
      '  | some op => some op',
      '  | none => X86ReturnCleanup.embed Doom.Verification.ExtractedQueryDispatch.linked pc',
      'theorem linked_checked : linked=E1M1AimProgramLink.program := by',
      '  funext pc',
      '  simp only [linked,E1M1AimProgramLink.program,',
      '    Doom.Verification.ExtractedAimCompletedReturn.linked_checked,',
      '    Doom.Verification.ExtractedQueryDispatch.program_checked]',
      '  cases E1M1AimCompletedReturn.program pc <;> rfl',
      ''])
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('Doom.Proofs.E1M1AimProgramLink.program','linked').replace('E1M1AimProgramLink.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'linked' in decl:source+='rw [linked_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".linked_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.linked_checked']
    names+=[NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-linked-query';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimLinkedQuery'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='One continuous execution under a single authenticated instruction map, from path-query entry through collection, ordered hits, and DOS caller return. The union preserves both complete maps: 3992 addresses in added regions are checked by kernel reduction, and all other natural-number addresses reduce symbolically to a common core. Returned slope matches production afterPath on the actual pathTraverse result and caller values restore from query-entry memory. Initial representation, successful visitation, pointer validity, arithmetic availability, earlier aim setup/ray and reachable E1M1 justification remain open. No runtime, decoder or instruction-semantic changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: compatible program union and continuous query-to-caller execution; strict axiom audit.')
if __name__=='__main__':main()

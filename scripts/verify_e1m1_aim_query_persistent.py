#!/usr/bin/env python3
"""Certify the setup-created callback slot and complete first-entry invariant."""
import argparse,json,re,subprocess
import verify_e1m1_aim_query_catalog as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimFirstSlot':['execution'], 'E1M1AimQuerySlot':['execution'],
 'E1M1AimEntryPersistent':['layout','query_safe','slot_marks','resolver','persistent'],
 'E1M1AimQueryPersistent':['execution']}
QUERY_ARGS='q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe argument cursorCall room'
CONTRACTS=[
 ('E1M1AimFirstSlot','execution','s f hits resolve bounded limit encoded protect callback'),
 ('E1M1AimQuerySlot','execution',QUERY_ARGS),
 ('E1M1AimEntryPersistent','layout','s t hits sameStack safe'),
 ('E1M1AimEntryPersistent','query_safe','s out hits lookup base fraction j bounded stack selection safe'),
 ('E1M1AimEntryPersistent','slot_marks','q hits bounded separated'),
 ('E1M1AimEntryPersistent','resolver','lines objects hit'),
 ('E1M1AimEntryPersistent','persistent','q s out hits portals distance z initial bounded separated outcome live frame slot'),
 ('E1M1AimQueryPersistent','execution',QUERY_ARGS+' portals distance z initial')]
NAMESPACE='Doom.Verification.ExtractedAimQueryPersistent'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Layout':'E1M1AimCycleInvariant','QuerySafe':'E1M1AimCycleInvariant',
      'Initial':'E1M1AimEntryPersistent','view':'E1M1AimQueryCatalog',
      'Portal':'E1M1AimCatalog','StableWord':'E1M1AimMapFrame',
      'Outcome':'E1M1AimFirstSelection','address':'E1M1MinimumScan',
      'result':'E1M1InterceptSetup','program':'E1M1FirstIntercept',
      'Protected':'E1M1AimFirstSelection' if module=='E1M1AimFirstSlot' else 'E1M1TraversalEntry'}
    if module=='E1M1AimEntryPersistent':owners['resolve']='E1M1ThingFinish'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimQueryPersistent\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='''
def queryProgram := Doom.Verification.ExtractedQueryDispatch.linked
theorem queryProgram_checked : queryProgram=E1M1FirstIntercept.program :=
  Doom.Verification.ExtractedQueryDispatch.program_checked
'''
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('Doom.Proofs.E1M1FirstIntercept.program','queryProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'queryProgram []' in decl:source+='rw [queryProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms queryProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".queryProgram_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.queryProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-query-persistent';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimQueryPersistent'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous path-query initialization/collection/setup/scan derives the created callback slot and every field of the live Persistent invariant. Slot protection follows from initial record separation, current EBX query protection from actual selection, and fraction-mark resolver stability from the real resolver definition. Initial layout, read-protected portal image and range/eye values are still required for the collection produced by the pure source run. No reached-state invariant or callback-slot premise in the combined query execution. Full query-through-return program linkage, other caller contracts, earlier aim setup/ray and reachable E1M1 justification remain open. No runtime, new bytes or instruction-semantic changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: continuous query derives full live-entry Persistent invariant; strict axiom audit.')
if __name__=='__main__':main()

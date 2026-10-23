#!/usr/bin/env python3
"""Certify query-to-caller composition with initial-only entry contracts."""
import argparse,json,re,subprocess
import verify_e1m1_aim_query_persistent as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimCallerCursor':['cursor_safe','restores','execution'],
 'E1M1AimReadyCaller':['execution'],
 'E1M1AimQueryCaller':['restores','execution']}
QUERY_ARGS=previous.QUERY_ARGS
CONTRACTS=[
 ('E1M1AimCallerCursor','cursor_safe','base off safe member'),
 ('E1M1AimCallerCursor','restores','start finish base image stack protect'),
 ('E1M1AimCallerCursor','execution','initial resolve start finish base steps answer run exit nonnull image stack protect first second'),
 ('E1M1AimReadyCaller','execution','scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available base s outcome persistent bottom top actors wallCatalog targetSafe null protect cursorSafe shape nonnull first second'),
 ('E1M1AimQueryCaller','restores','q s f middle out frame reads restored'),
 ('E1M1AimQueryCaller','execution',QUERY_ARGS+' scene shooter thing distance portals walls who initial')]
NAMESPACE='Doom.Verification.ExtractedAimQueryCaller'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'CursorSafe':'E1M1AimCallerCursor','slots':'E1M1AimSavedCaller',
      'Image':'E1M1AimSavedCaller','Restores':'E1M1AimSavedCaller',
      'Initial':'E1M1AimQueryCaller','Source':'E1M1AimQueryCaller','callerSlots':'E1M1AimQueryCaller',
      'Portal':'E1M1AimCatalog','Represents':'E1M1AimSourceCatalog',
      'Available':'E1M1AimOrderedLoop','Catalog':'E1M1AimActorCatalog',
      'StableWord':'E1M1AimMapFrame','Shape':'E1M1AimStackShape',
      'Protected':'E1M1AimQueryCatalog'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimQueryCaller\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='''
def queryProgram := Doom.Verification.ExtractedQueryDispatch.linked
theorem queryProgram_checked : queryProgram=E1M1FirstIntercept.program :=
  Doom.Verification.ExtractedQueryDispatch.program_checked
def returnProgram := Doom.Verification.ExtractedAimCompletedReturn.linked
theorem returnProgram_checked : returnProgram=E1M1AimCompletedReturn.program :=
  Doom.Verification.ExtractedAimCompletedReturn.linked_checked
'''
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1FirstIntercept.program','queryProgram').replace('E1M1AimCompletedReturn.program','returnProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'queryProgram []' in decl:source+='rw [queryProgram_checked]\n  '
        if 'returnProgram []' in decl:source+='rw [returnProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms queryProgram_checked\n#print axioms returnProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".queryProgram_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.queryProgram_checked',NAMESPACE+'.returnProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-query-caller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimQueryCaller'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Query prefix and complete ordered-hit loop/return meet at the identical machine state. Actor/wall catalogs, live write protection, clipping globals and saved caller values are transported from initial query memory; terminal cases require only return cursor protection. The final slope matches production afterPath on the actual pathTraverse result, and saved caller restoration refers to query-entry memory. Two authenticated program maps remain explicit: single-map compatibility and continuous linkage are not yet proved. Initial source representation, successful visitation, pointer validity, arithmetic availability, earlier aim setup/ray and reachable E1M1 justification remain open. No runtime, decoder or instruction-semantic changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: query and complete caller share the actual boundary; strict axiom audit.')
if __name__=='__main__':main()

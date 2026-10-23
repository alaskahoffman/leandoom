#!/usr/bin/env python3
"""Certify protected memory through the complete aim call and next retry."""
import argparse,json,re,subprocess
import verify_e1m1_aim_retry_query as previous
import verify_e1m1_aim_target_decision as target
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimCallerFrame':['execution'], 'E1M1AimQueryFrame':['execution'],
 'E1M1AimCallFrame':['execution','retry']}
ENTRY_ARGS=previous.ENTRY_ARGS+' savedSafe returnSafe watched watchedRead watchedSafe'
CONTRACTS=[
 ('E1M1AimCallerFrame','execution',target.CALLER_ARGS+' watched watchedSafe watchedCursor'),
 ('E1M1AimQueryFrame','execution',target.QUERY_ARGS+' scene shooter thing distance portals walls who initial watched watchedRead watchedSafe'),
 ('E1M1AimCallFrame','execution',ENTRY_ARGS),
 ('E1M1AimCallFrame','retry',ENTRY_ARGS+' retrySafe second controller resume')]
NAMESPACE='Doom.Verification.ExtractedAimCallFrame'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Represents':'E1M1AimSourceCatalog','Available':'E1M1AimOrderedLoop',
      'Catalog':'E1M1AimActorCatalog','StableWord':'E1M1AimMapFrame','Shape':'E1M1AimStackShape',
      'Initial':'E1M1AimQueryCaller','Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'Protected':'E1M1AimQueryCatalog','view':'E1M1AimQueryCatalog','traversal':'E1M1PathMapQuery'}
    if module!='E1M1AimCallerFrame':owners['resolve']='E1M1ThingFinish'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimCallFrame\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimRetryQuery.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimRetryQuery.linked_checked',
      'def returnProgram := Doom.Verification.ExtractedAimCompletedReturn.linked',
      'theorem returnProgram_checked : returnProgram=E1M1AimCompletedReturn.program :=',
      '  Doom.Verification.ExtractedAimCompletedReturn.linked_checked',
      ''])
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1AimProgramLink.program','linked').replace('E1M1AimCompletedReturn.program','returnProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'linked' in decl:source+='rw [linked_checked]\n  '
        if 'returnProgram' in decl:source+='rw [returnProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n#print axioms returnProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".linked_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.linked_checked',NAMESPACE+'.returnProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-call-frame';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimCallFrame'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The continuous aim-entry execution and conditional miss-to-retry now preserve any finite list of protected memory words, alongside the production aim result, returned target and original caller registers. Protection before ray setup, during collection, during callbacks/returns and across the two retry stores is explicit at initial memory/address views. No memory equality at a reached state is assumed. This supplies a reusable whole-call frame for map/object/table data; instantiating all next-probe contracts and tracking intentionally changed stamps/epoch remains open. No next probe is executed here; reachable E1M1 and whole-game parity remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: protected words survive the complete aim call and actual retry; strict axiom audit.')
if __name__=='__main__':main()

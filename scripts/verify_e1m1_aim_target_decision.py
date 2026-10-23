#!/usr/bin/env python3
"""Certify returned target provenance and the actual autoaim decision after a continuous query."""
import argparse,json,re,subprocess
import verify_e1m1_aim_linked_query as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimReturnedTarget':['word','returned','probe','zero_slope_hit'],
 'E1M1AimTargetCaller':['execution'], 'E1M1AimQueryTarget':['execution'],
 'E1M1AimTargetDecision':['contains','decision','execution']}
QUERY_ARGS=previous.QUERY_ARGS
CALLER_ARGS='scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available base s outcome persistent bottom top actors wallCatalog targetSafe null protect cursorSafe shape nonnull first second'
CONTRACTS=[
 ('E1M1AimReturnedTarget','word','s a safe'),
 ('E1M1AimReturnedTarget','returned','initial resolve s answer exit'),
 ('E1M1AimReturnedTarget','probe','initial resolve out answer image nonnull value'),
 ('E1M1AimReturnedTarget','zero_slope_hit','out answer related hit zero'),
 ('E1M1AimTargetCaller','execution',CALLER_ARGS),
 ('E1M1AimQueryTarget','execution',QUERY_ARGS+' scene shooter thing distance portals walls who initial'),
 ('E1M1AimTargetDecision','contains','pc present'),
 ('E1M1AimTargetDecision','decision','second out answer related resume'),
 ('E1M1AimTargetDecision','execution',QUERY_ARGS+' scene shooter thing distance portals walls who initial second resume')]
NAMESPACE='Doom.Verification.ExtractedAimTargetDecision'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Image':'E1M1AimReturnedTarget','Represents':'E1M1AimSourceCatalog',
      'Available':'E1M1AimOrderedLoop','Catalog':'E1M1AimActorCatalog',
      'StableWord':'E1M1AimMapFrame','Shape':'E1M1AimStackShape',
      'Initial':'E1M1AimQueryCaller','Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog'}
    if module=='E1M1AimQueryTarget':owners['resolve']='E1M1ThingFinish'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimTargetDecision\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimLinkedQuery.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimLinkedQuery.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-target-decision';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTargetDecision'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous query preserves the returned target record/pointer image and derives the existing controller ProbeResult for the same execution, including a valid target with zero slope. Actual four-instruction controller decision and bullet-slope store are appended under the same authenticated map; initial saved return memory supplies the landing PC. One center/right probe stops or retries according to the source target presence. This does not execute every retry or all three probes. Initial representation, source success, pointer validity and arithmetic/memory contracts, earlier aim setup/ray, and reachable E1M1 justification remain open. No runtime, decoder or instruction-semantic changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: derived target/slope interface and actual post-query controller decision; strict axiom audit.')
if __name__=='__main__':main()

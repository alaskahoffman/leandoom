#!/usr/bin/env python3
"""Certify the complete three-query autoaim suffix and its production source result."""
import argparse,json,re,subprocess
import verify_e1m1_aim_pair_controller as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1AimIteration (LoopState visit remaining)\n'
GROUPS={'E1M1AimMissZero': ['empty_good', 'miss_good', 'hit_good', 'visit_good', 'loop_good', 'remaining_zero', 'aim'], 'E1M1AimThirdCall': ['prepared', 'inputs', 'execution'], 'E1M1AimThreeCalls': ['execution']}
CONTRACTS=[('E1M1AimMissZero', 'empty_good', 'top bottom history'), ('E1M1AimMissZero', 'miss_good', 'path top bottom history'), ('E1M1AimMissZero', 'hit_good', 'slope id path window top bottom history'), ('E1M1AimMissZero', 'visit_good', 'scene shooter thing path distance i state step run'), ('E1M1AimMissZero', 'loop_good', 'scene shooter thing path distance indices state final good run'), ('E1M1AimMissZero', 'remaining_zero', 'scene shooter thing path distance indices lower upper history answer run absent'), ('E1M1AimMissZero', 'aim', 'scene shooter angle distance answer run absent'), ('E1M1AimThirdCall', 'prepared', 'q s third thing facing cells h request tables data kept safe'), ('E1M1AimThirdCall', 'inputs', 'q s third thing facing cells h request data epoch fresh'), ('E1M1AimThirdCall', 'execution', 'q pick s third thing facing h request epoch fresh shooter shooterValue profile xout yout okX okY common height statics scenes tables data separated callbackSafe cursorCall room portals walls who watched covered kept initial savedSafe returnSafe watchedRead watchedSafe stampSafe stampProtected'), ('E1M1AimThreeCalls', 'execution', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial')]
NAMESPACE='Doom.Verification.ExtractedAimThreeCalls'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Source':'E1M1AimQueryCaller','resolve':'E1M1ThingFinish',
      'traversal':'E1M1PathMapQuery','nextAngle':'E1M1AimRetryGeometry',
      'reads':'E1M1AimRetryInputs','Image':'E1M1AimStampImage','Fresh':'E1M1AimStampImage',
      'stampWords':'E1M1AimStampQuery',
      'Read':'E1M1AimPreRayMemory','Later':'E1M1AimPreRayMemory','layout':'E1M1AimPreRayMemory',
      'view':'E1M1AimQueryCatalog','Prepared':'E1M1AimRetryInputs',
      'context':'E1M1AimNextContext','route':'E1M1AimNextContext'}
    if module=='E1M1AimThirdCall':
        owners.update({word:module for word in ['angle','context','route','Request']})
    if module=='E1M1AimMissZero':
        owners['Good']=module
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimThreeCalls\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimPairController.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimPairController.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-three-calls';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimThreeCalls'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='From the original center aim-call entry, the joined theorem executes every required query and returns from the autoaim controller. It proves the production Scene.bulletAim selection and identical stored slope on center hit, right hit, left hit and all-miss paths. The third geometry, payload and catalog are reconstructed from preserved original-memory reads; its counter and freshness follow from the two executed stamp histories. A separate source-loop invariant establishes zero slope for every successful miss, without a division-success or zero-result assumption. This remains conditional on original map/object/catalog representation, source arithmetic, route capacity, freshness and memory separation. The controller prologue and reachable E1M1 invariants are not discharged. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: three executed aim queries, source selection and controller return joined; strict inherited axiom audit.')
if __name__=='__main__':main()

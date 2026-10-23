#!/usr/bin/env python3
"""Certify direct actor-pointer correspondence through the complete three-probe controller."""
import argparse,json,re,subprocess
import verify_e1m1_aim_actor_decision as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1AimIteration (LoopState visit remaining)\n'
GROUPS={'E1M1AimActorCallerFrame': ['execution'], 'E1M1AimActorStampQuery': ['execution'], 'E1M1AimActorStampCall': ['execution', 'retry'], 'E1M1AimActorNextCall': ['execution'], 'E1M1AimActorRetryPair': ['execution'], 'E1M1AimActorPairController': ['execution'], 'E1M1AimActorThirdCall': ['execution'], 'E1M1AimActorController': ['suffix', 'execution']}
PREVIOUS_MODULES={'E1M1AimActorCallerFrame': 'E1M1AimCallerFrame', 'E1M1AimActorStampQuery': 'E1M1AimStampQuery', 'E1M1AimActorStampCall': 'E1M1AimStampCall', 'E1M1AimActorNextCall': 'E1M1AimNextCall', 'E1M1AimActorRetryPair': 'E1M1AimRetryPair', 'E1M1AimActorPairController': 'E1M1AimPairController', 'E1M1AimActorThirdCall': 'E1M1AimThirdCall', 'E1M1AimActorController': 'E1M1AimSelectedCall'}
CONTRACTS=[('E1M1AimActorCallerFrame', 'execution', 'scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available base s outcome persistent bottom top actors wallCatalog targetSafe null protect cursorSafe shape nonnull first second watched watchedSafe watchedCursor'), ('E1M1AimActorStampQuery', 'execution', 'q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe argument cursorCall room scene shooter thing distance portals walls who initial watched watchedRead watchedSafe stampSafe stampProtected'), ('E1M1AimActorStampCall', 'execution', 'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe watched watchedRead watchedSafe stampSafe stampProtected'), ('E1M1AimActorStampCall', 'retry', 'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe watched watchedRead watchedSafe retrySafe second controller resume stampSafe stampProtected stampRetry'), ('E1M1AimActorNextCall', 'execution', 'q pick s next thing angle distance second h request seen size image before nextX nextY okX okY data profile common height statics scenes room shooter shooterValue controller separated callbackSafe cursorCall portals walls who watched kept initial savedSafe returnSafe watchedRead watchedSafe stampSafe stampProtected'), ('E1M1AimActorRetryPair', 'execution', 'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe second nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial'), ('E1M1AimActorPairController', 'execution', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial'), ('E1M1AimActorThirdCall', 'execution', 'q pick s third thing facing h request epoch fresh shooter shooterValue profile xout yout okX okY common height statics scenes tables data separated callbackSafe cursorCall room portals walls who watched covered kept initial savedSafe returnSafe watchedRead watchedSafe stampSafe stampProtected'), ('E1M1AimActorController', 'suffix', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered'), ('E1M1AimActorController', 'execution', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered tableSafe freshSafe value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimActorController'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Represents':'E1M1AimSourceCatalog','Available':'E1M1AimOrderedLoop',
      'Catalog':'E1M1AimActorCatalog','StableWord':'E1M1AimMapFrame','Shape':'E1M1AimStackShape',
      'Initial':'E1M1AimQueryCaller','Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'view':'E1M1AimQueryCatalog','stampWords':'E1M1AimStampQuery',
      'traversal':'E1M1PathMapQuery','nextAngle':'E1M1AimRetryGeometry',
      'reads':'E1M1AimRetryInputs','Prepared':'E1M1AimRetryInputs',
      'context':'E1M1AimNextContext','route':'E1M1AimNextContext'}
    if module!='E1M1AimActorCallerFrame':owners['resolve']='E1M1ThingFinish'
    if module=='E1M1AimActorThirdCall':
        owners.update({key:'E1M1AimThirdCall' for key in ['angle','context','route','Request']})
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorController\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimActorDecision.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimActorDecision.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-actor-controller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorController'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The stronger actor-tagged target image is threaded through watched-memory query returns, exact stamp histories, pre-ray setup, actual retries, and all three autoaim probes. The continuous theorem starts at P_BulletSlope entry 0x2d7c0, executes its prologue and actual short-circuit paths, and returns to the original caller with matching source selection, bullet slope, stack and saved registers. After the final return, a selected source window implies targetGlobal=objects(window.target) and matching conditional aim slope; no selected window implies a null target, allowing the historical stale aim-slope global. All ten strengthened signatures retain their predecessors exact input binders; no reached answer or pointer-equality premise is added. Remaining original-memory transport, map/object/catalog, arithmetic, capacity, freshness, separation and reachable E1M1 justification are still open. No runtime, decoder, instruction-semantic or binary-range changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exact actor-pointer observation through all three probes and original caller return; strict inherited axiom audit.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify the returned autoaim target image and pre-prologue table/freshness transport."""
import argparse,json,re,subprocess
import verify_e1m1_aim_controller_call as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1AimIteration (LoopState visit remaining)\n'
GROUPS={'E1M1AimWindowTarget': ['empty_good', 'miss_good', 'hit_good', 'visit_good', 'loop_good', 'remaining_target', 'aim'], 'E1M1AimControllerTarget': ['frame', 'accepted', 'last', 'selection', 'miss', 'last_correspondence'], 'E1M1AimControllerData': ['tables', 'fresh', 'counter'], 'E1M1AimSelectedCall': ['suffix', 'execution']}
CONTRACTS=[('E1M1AimWindowTarget', 'empty_good', 'top bottom history'), ('E1M1AimWindowTarget', 'miss_good', 'path top bottom history'), ('E1M1AimWindowTarget', 'hit_good', 'slope window path top bottom history'), ('E1M1AimWindowTarget', 'visit_good', 'scene shooter thing path distance i state step run'), ('E1M1AimWindowTarget', 'loop_good', 'scene shooter thing path distance indices state final good run'), ('E1M1AimWindowTarget', 'remaining_target', 'scene shooter thing path distance indices lower upper history answer run'), ('E1M1AimWindowTarget', 'aim', 'scene shooter angle distance answer run'), ('E1M1AimControllerTarget', 'frame', 'initial resolve out next answer image target slope'), ('E1M1AimControllerTarget', 'accepted', 'second initial resolve out answer image'), ('E1M1AimControllerTarget', 'last', 'initial resolve out answer image'), ('E1M1AimControllerTarget', 'selection', 'scene shooter facing probe offset answer initial resolve out query image'), ('E1M1AimControllerTarget', 'miss', 'initial resolve out answer facing image absent'), ('E1M1AimControllerTarget', 'last_correspondence', 'scene shooter angle a b c out initial resolve p0 p1 p2 no0 no1 related image'), ('E1M1AimControllerData', 'tables', 's f before safe'), ('E1M1AimControllerData', 'fresh', 's f lines epoch count before safe'), ('E1M1AimControllerData', 'counter', 's f epoch before safe'), ('E1M1AimSelectedCall', 'suffix', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered'), ('E1M1AimSelectedCall', 'execution', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered tableSafe freshSafe value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimSelectedCall'

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
    if module=='E1M1AimWindowTarget':
        owners['Good']=module
        owners['StepGood']=module
    if module=='E1M1AimControllerTarget':
        owners['Image']='E1M1AimReturnedTarget'
        owners['Observed']=module
        # resolve is an explicit parameter here, not the imported encoding.
        del owners['resolve']
    if module=='E1M1AimControllerData':
        owners.update({'entry':'E1M1AimControllerEntry','writes':'E1M1AimControllerEntry','TableSafe':module})
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimSelectedCall\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimControllerCall.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimControllerCall.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-selected-call';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSelectedCall'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The continuous controller-entry-to-caller proof now exports the original collected-record target encoding after every return. A successful source query has target equal to its window target; the source identity is derived from the live finite hit loop. After store/pops/RET, no selected window implies a null DOS target; a selected window supplies a collected-record witness with the same ID, exact encoded pointer, and matching conditional aim-slope global. This retains the older image witness and does not newly prove that witness is an actor-kind intercept or replace it by objects(window.target). Trig tables and both future stamp-freshness assumptions are now supplied from pre-prologue memory and transported through the five stack writes; current-counter transport is separately proved. Other query representation/catalog/arithmetic, capacity and separation assumptions remain at the deterministic first-call state, and reachable E1M1 invariants remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: returned selected-target image and original-memory table/freshness transport joined; strict inherited axiom audit.')
if __name__=='__main__':main()

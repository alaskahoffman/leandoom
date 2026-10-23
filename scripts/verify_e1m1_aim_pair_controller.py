#!/usr/bin/env python3
"""Certify center/right autoaim exits and the executed third request with two-history freshness."""
import argparse,json,re,subprocess
import verify_e1m1_aim_retry_pair as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimControllerExit': ['accepted', 'last', 'center', 'right'],
 'E1M1AimThirdRequest': ['two_ahead_ne', 'consecutive_fresh', 'retry_image', 'retry_fresh', 'arguments'],
 'E1M1AimPairController': ['execution']}
CONTRACTS=[('E1M1AimControllerExit', 'accepted', 'second out answer related hit resume'),
 ('E1M1AimControllerExit', 'last', 'out answer related resume'),
 ('E1M1AimControllerExit', 'center', 'scene shooter angle out answer query related hit resume'),
 ('E1M1AimControllerExit', 'right', 'scene shooter angle first answer out p0 p1 miss related hit resume'),
 ('E1M1AimThirdRequest', 'two_ahead_ne', 'epoch'),
 ('E1M1AimThirdRequest',
  'consecutive_fresh',
  'origin middle current lines epoch first second count firstSize secondSize firstImage secondImage before'),
 ('E1M1AimThirdRequest', 'retry_image', 'second origin out lines epoch seen count size image safe'),
 ('E1M1AimThirdRequest', 'retry_fresh', 'second out lines future count fresh safe'),
 ('E1M1AimThirdRequest', 'arguments', 's right third angle first second controller'),
 ('E1M1AimPairController',
  'execution',
  'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated '
  'callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra '
  'watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY '
  'nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial')]
NAMESPACE='Doom.Verification.ExtractedAimPairController'

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
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimPairController\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimRetryPair.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimRetryPair.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-pair-controller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimPairController'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The continuous center/right execution now closes the production bulletAim result on either target-present branch, including the original slope store, branch and controller RET. Double misses execute the real third CALL, deriving the original-angle left offset, shooter, range, stack and return word. Exact stamp histories through both completed queries and original two-ahead freshness establish fresh third-entry stamps, including modular wrap. Watched words and the second-query stamp image survive the third CALL. The final probe store/return is separately authenticated but its query body is not joined here. Source arithmetic/catalog contracts, route capacity, representation, original freshness and memory separation remain explicit. Controller prologue, third query body, all-miss source closure and reachable E1M1 invariants remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: center/right live autoaim exits and fresh third request joined; strict inherited axiom audit.')
if __name__=='__main__':main()

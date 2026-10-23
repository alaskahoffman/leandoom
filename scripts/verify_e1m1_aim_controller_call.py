#!/usr/bin/env python3
"""Certify autoaim from the original controller entry through caller restoration."""
import argparse,json,re,subprocess
import verify_e1m1_aim_three_calls as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1AimIteration (LoopState visit remaining)\n'
GROUPS={'E1M1AimControllerEntry': ['execution', 'memory', 'frame', 'arguments', 'saved'], 'E1M1AimControllerFrame': ['finished', 'accepted', 'last', 'retry_registers', 'caller'], 'E1M1AimControllerCall': ['suffix', 'execution']}
CONTRACTS=[('E1M1AimControllerEntry', 'execution', 's f'), ('E1M1AimControllerEntry', 'memory', 's f'), ('E1M1AimControllerEntry', 'frame', 's f a safe'), ('E1M1AimControllerEntry', 'arguments', 's f angle value safe'), ('E1M1AimControllerEntry', 'saved', 's f'), ('E1M1AimControllerFrame', 'finished', 's t f stack bp di words'), ('E1M1AimControllerFrame', 'accepted', 'second s out stack bp di words safe'), ('E1M1AimControllerFrame', 'last', 's out stack bp di words safe'), ('E1M1AimControllerFrame', 'retry_registers', 'second s'), ('E1M1AimControllerFrame', 'caller', 's f out restored'), ('E1M1AimControllerCall', 'suffix', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered'), ('E1M1AimControllerCall', 'execution', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimControllerCall'

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
    if module=='E1M1AimControllerEntry':
        owners.update({word:module for word in ['entry','writes']})
    if module=='E1M1AimControllerFrame':
        owners.update({word:module for word in ['offsets','slots','Restores']})
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimControllerCall\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimThreeCalls.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimThreeCalls.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-controller-call';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimControllerCall'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The authenticated nine-instruction controller prologue now joins all required queries and the final controller return. The theorem starts at P_BulletSlope entry 0x2d7c0 and derives the first request from the original actor angle. It proves the production Scene.bulletAim selection, identical stored slope, restored outer return PC and stack, and restored EBX/ECX/EDX/ESI/EBP/EDI on all four outcomes. Five caller stack words are preserved through actual queries, retry stores and the final slope store by explicit watched-word coverage and separation. Query representation, catalog/arithmetic, capacity and freshness contracts remain at the deterministically constructed first-call state; they are not yet transported wholesale to pre-prologue original memory or established for reachable E1M1 play. Post-return exact target encoding and full global-state correspondence remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original autoaim entry, complete query controller and caller restoration joined; strict inherited axiom audit.')
if __name__=='__main__':main()

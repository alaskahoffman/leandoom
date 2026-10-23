#!/usr/bin/env python3
"""Certify actor-tagged ordered hits, direct object pointers, and the real controller decision."""
import argparse,json,re,subprocess
import verify_e1m1_aim_selected_call as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1AimIteration (LoopState visit remaining)\n'
GROUPS={'E1M1AimActorHit': ['weaken', 'execution'], 'E1M1AimActorOrdered': ['execution', 'initial'], 'E1M1AimActorCaller': ['weaken', 'returned', 'object_pointer', 'execution'], 'E1M1AimActorQuery': ['execution'], 'E1M1AimActorObservation': ['frame', 'accepted', 'last', 'selection', 'miss', 'last_correspondence'], 'E1M1AimActorDecision': ['decision_image', 'execution']}
CONTRACTS=[('E1M1AimActorHit', 'weaken', 'initial resolve out answer exit'), ('E1M1AimActorHit', 'execution', 'scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query a s f seen visits sp fraction j history selection before bottom top actors wallCatalog arithmetic null targetSafe'), ('E1M1AimActorOrdered', 'execution', 'scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available watched fuel a origin s seen visits budget history boundary bottom top ready null base shape'), ('E1M1AimActorOrdered', 'initial', 'scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available watched origin s aligned bottom top actors wallCatalog targetSafe null protect base shape'), ('E1M1AimActorCaller', 'weaken', 'initial resolve out answer image'), ('E1M1AimActorCaller', 'returned', 'initial resolve s answer exit'), ('E1M1AimActorCaller', 'object_pointer', 'initial lines objects out answer image id chosen'), ('E1M1AimActorCaller', 'execution', 'scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query available base s outcome persistent bottom top actors wallCatalog targetSafe null protect cursorSafe shape nonnull first second'), ('E1M1AimActorQuery', 'execution', 'q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe argument cursorCall room scene shooter thing distance portals walls who initial'), ('E1M1AimActorObservation', 'frame', 'initial resolve out next answer image target slope'), ('E1M1AimActorObservation', 'accepted', 'second initial resolve out answer image'), ('E1M1AimActorObservation', 'last', 'initial resolve out answer image'), ('E1M1AimActorObservation', 'selection', 'scene shooter facing probe offset answer initial lines objects out query image'), ('E1M1AimActorObservation', 'miss', 'initial lines objects out answer facing image absent'), ('E1M1AimActorObservation', 'last_correspondence', 'scene shooter angle a b c out initial lines objects p0 p1 p2 no0 no1 related image'), ('E1M1AimActorDecision', 'decision_image', 'second initial resolve out answer image'), ('E1M1AimActorDecision', 'execution', 'q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe argument cursorCall room scene shooter thing distance portals walls who initial second resume')]
NAMESPACE='Doom.Verification.ExtractedAimActorDecision'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Represents':'E1M1AimSourceCatalog','Available':'E1M1AimOrderedLoop',
      'Catalog':'E1M1AimActorCatalog','StableWord':'E1M1AimMapFrame','Shape':'E1M1AimStackShape',
      'Initial':'E1M1AimQueryCaller','Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'Position':'E1M1AimPortalPrefix','Boundary':'E1M1AimActorBoundary',
      'Arithmetic':'E1M1AimHitOutcome','Ready':'E1M1AimMixedExit','AlignedNext':'E1M1AimSynchronizedCycle',
      'Exit':'E1M1AimActorHit','Outcome':'E1M1AimActorHit','Image':'E1M1AimActorCaller',
      'Observed':'E1M1AimActorObservation','program':'E1M1AimActorSelect'}
    if module in {'E1M1AimActorQuery','E1M1AimActorDecision'} and name=='execution':
        owners['resolve']='E1M1ThingFinish'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorDecision\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimSelectedCall.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimSelectedCall.linked_checked',
      'def returnProgram := Doom.Verification.ExtractedAimCompletedReturn.linked',
      'theorem returnProgram_checked : returnProgram=E1M1AimCompletedReturn.program :=',
      '  Doom.Verification.ExtractedAimCompletedReturn.linked_checked',
      'def actorProgram := Doom.Verification.ExtractedAimActorSelect.linked',
      'theorem actorProgram_checked : actorProgram=E1M1AimActorSelect.program :=',
      '  Doom.Verification.ExtractedAimActorSelect.linked_checked',
      ''])
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1AimProgramLink.program','linked').replace('E1M1AimCompletedReturn.program','returnProgram').replace('Doom.Proofs.E1M1AimActorSelect.program','actorProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'linked' in decl:source+='rw [linked_checked]\n  '
        if 'returnProgram' in decl:source+='rw [returnProgram_checked]\n  '
        if 'actorProgram' in decl:source+='rw [actorProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n#print axioms returnProgram_checked\n#print axioms actorProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".linked_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.linked_checked',NAMESPACE+'.returnProgram_checked',NAMESPACE+'.actorProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-actor-decision';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorDecision'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The actual exhaustive callback now retains the selected actor tag; ordered-loop induction and the complete query return preserve it. The same initial query contracts derive an actor-tagged returned image, which resolves directly to objects(source target ID), without assuming disjoint line/actor IDs or post-execution pointer equality. Continuous collection entry through the real center/right controller decision exports this pointer and conditional aim-slope equality. Strong-image adapters preserve it through accepted/final returns and translate actual source windows to direct object pointers, including all-miss stale-slope behavior. These adapters are not yet substituted throughout the complete prologue/three-probe aggregate; that older theorem still exports its weaker record image. Map/object/catalog, arithmetic, capacity, separation and reachable-state obligations remain open. No runtime, decoder, instruction-semantic or binary-range changes; emulator checks inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actor provenance, direct object-pointer query/decision correspondence, and controller adapters; strict inherited axiom audit.')
if __name__=='__main__':main()

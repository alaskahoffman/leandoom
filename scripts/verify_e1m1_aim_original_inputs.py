#!/usr/bin/env python3
"""Certify full aiming correspondence from original-memory input contracts."""
import argparse,json,re,subprocess
import verify_e1m1_aim_actor_controller as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1AimIteration (LoopState visit remaining)\n'
GROUPS={'E1M1AimControllerInputs': ['registers', 'kept', 'map', 'payload', 'catalog'], 'E1M1AimControllerSetup': ['setup'], 'E1M1AimOriginalInputs': ['execution']}
CONTRACTS=[('E1M1AimControllerInputs', 'registers', 's f angle value safe'), ('E1M1AimControllerInputs', 'kept', 's f angle addresses safe'), ('E1M1AimControllerInputs', 'map', 's f angle base lines words width height regs before safe'), ('E1M1AimControllerInputs', 'payload', 'q c s f angle regs before safe'), ('E1M1AimControllerInputs', 'catalog', 'q s f angle scene shooter hits portals walls who regs before safe'), ('E1M1AimControllerSetup', 'setup', 'q s f thing angle regs before tables safe'), ('E1M1AimOriginalInputs', 'execution', 'q pick s f thing angle h shooter shooterValue profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe nextPick nextX nextY tables nextData extra watchedRead watchedSafe retrySafe stampSafe stampProtected stampRetry before beforeTwo nextOkX nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial thirdPick thirdX thirdY thirdOkX thirdOkY thirdStatics thirdScenes thirdData thirdRoom thirdPortals thirdWalls thirdCovered thirdInitial stackCovered setupSafe tableSafe freshSafe value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimOriginalInputs'

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
    owners.update({'entry':'E1M1AimControllerEntry','layout':'E1M1AimControllerInputs',
      'SafeReads':'E1M1AimControllerInputs','resolve':'E1M1ThingFinish'})
    if module=='E1M1AimControllerSetup':owners['reads']='E1M1AimControllerSetup'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimOriginalInputs\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimActorController.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimActorController.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-original-inputs';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimOriginalInputs'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='The continuous three-probe aiming theorem now takes all memory input predicates from original controller-entry memory. A pure register layout expresses future stack and call-register guards without writing memory. The real prologue registers are proved equal to that layout, and finite read separation from its five stack stores transports geometry, blockmap words, cell payloads, actor/opening catalogs, current counter and stamp freshness. The full entry-to-return result retains exact source selection, direct actor pointer, conditional aim slope, stored bullet slope and caller restoration. New guards explicitly protect the transported reads; no later memory image or reached query answer is assumed. Reachable E1M1 representation, arithmetic success, capacities, freshness and separation remain obligations, as does a wider global memory frame. No runtime, decoder, instruction-semantic or binary-range changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original-memory query inputs transported and joined to complete aiming; strict inherited axiom audit.')
if __name__=='__main__':main()

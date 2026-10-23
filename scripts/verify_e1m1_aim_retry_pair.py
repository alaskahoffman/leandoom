#!/usr/bin/env python3
"""Certify initial-memory catalog transfer and two complete aim calls joined by the real retry."""
import argparse,json,re,subprocess
import verify_e1m1_aim_retry_collection as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimRetryCatalog': ['actor_reads',
                         'wall_reads',
                         'portal_reads',
                         'later',
                         'read',
                         'callback',
                         'saved',
                         'initial'],
 'E1M1AimNextCall': ['execution'],
 'E1M1AimRetryPair': ['execution']}
CONTRACTS=[('E1M1AimRetryCatalog', 'actor_reads', 'hits lookup portals i hi kind a member'),
 ('E1M1AimRetryCatalog', 'wall_reads', 'hits lookup portals i hi kind'),
 ('E1M1AimRetryCatalog', 'portal_reads', 'hits lookup portals i hi p listed a member'),
 ('E1M1AimRetryCatalog', 'later', 'q s t a stack h'),
 ('E1M1AimRetryCatalog', 'read', 'q s t a stack h'),
 ('E1M1AimRetryCatalog', 'callback', 'q s t stack h'),
 ('E1M1AimRetryCatalog', 'saved', 's t stack h'),
 ('E1M1AimRetryCatalog', 'initial', 'q s t scene shooter hits portals walls who stack actor h kept'),
 ('E1M1AimNextCall',
  'execution',
  'q pick s next thing angle distance second h request seen size image before nextX nextY okX okY data profile common height '
  'statics scenes room shooter shooterValue controller separated callbackSafe cursorCall portals walls who watched kept initial '
  'savedSafe returnSafe watchedRead watchedSafe stampSafe stampProtected'),
 ('E1M1AimRetryPair',
  'execution',
  'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes '
  'payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe second nextPick nextX nextY '
  'tables nextData extra watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry before nextOkX '
  'nextOkY nextStatics nextScenes nextRoom nextPortals nextWalls nextInitial')]
NAMESPACE='Doom.Verification.ExtractedAimRetryPair'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Source':'E1M1AimQueryCaller','resolve':'E1M1ThingFinish',
      'traversal':'E1M1PathMapQuery','nextAngle':'E1M1AimRetryGeometry',
      'reads':('E1M1AimRetryCatalog' if module=='E1M1AimRetryCatalog' else 'E1M1AimRetryInputs'),
      'Read':'E1M1AimPreRayMemory','Later':'E1M1AimPreRayMemory','layout':'E1M1AimPreRayMemory',
      'view':'E1M1AimQueryCatalog','Prepared':'E1M1AimRetryInputs',
      'context':'E1M1AimNextContext','route':'E1M1AimNextContext'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimRetryPair\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimRetryCollection.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimRetryCollection.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-retry-pair';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimRetryPair'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Finite actor/wall/portal catalog reads are transported from original memory through the complete first call and actual miss-controlled retry. Static guards transfer using the restored stack, while setup produces new shooter/range/clipping/target globals. The next full aim call reuses generated collection, ordered line/actor processing and the original return, yielding the source target and slope and exact next-origin stamp image. The joined authenticated execution covers two complete calls and the intervening retry, with the exact controller return address. Next source catalog coverage/arithmetic availability, initial representation, successful divisions, route capacity, freshness and memory/write separation remain explicit contracts. The full three-probe controller and reachable E1M1 invariants remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: initial-memory catalogs and complete next aim/return joined across the real retry; strict inherited axiom audit.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify exact stamp history from aim entry through retry and next initialization."""
import argparse,json,re,subprocess
import verify_e1m1_aim_stamp_query as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimStampOrigin': ['rebase', 'history_size', 'preray'],
 'E1M1AimStampCall': ['execution', 'retry'],
 'E1M1AimStampRestart': ['restart', 'retry']}
CONTRACTS=[('E1M1AimStampOrigin', 'rebase', 'before origin current lines epoch seen image kept'),
 ('E1M1AimStampOrigin', 'history_size', 'q seen cells'),
 ('E1M1AimStampOrigin', 'preray', 'q s thing angle distance h out seen size image'),
 ('E1M1AimStampCall',
  'execution',
  'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes '
  'payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe watched watchedRead '
  'watchedSafe stampSafe stampProtected'),
 ('E1M1AimStampCall',
  'retry',
  'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes '
  'payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe watched watchedRead '
  'watchedSafe retrySafe second controller resume stampSafe stampProtected stampRetry'),
 ('E1M1AimStampRestart',
  'restart',
  'q s next thing angle distance second cells h request data seen size image before nextX nextY okX okY'),
 ('E1M1AimStampRestart',
  'retry',
  'q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes '
  'payloads separated callbackSafe cursorCall room portals walls who initial savedSafe returnSafe second nextCells tables '
  'nextData watchedRead watchedSafe retrySafe controller resume stampSafe stampProtected stampRetry')]
NAMESPACE='Doom.Verification.ExtractedAimStampRestart'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Source':'E1M1AimQueryCaller','resolve':'E1M1ThingFinish',
      'traversal':'E1M1PathMapQuery','nextAngle':'E1M1AimRetryGeometry',
      'reads':'E1M1AimRetryInputs','Prepared':'E1M1AimRetryInputs'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimStampRestart\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimStampQuery.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimStampQuery.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-stamp-restart';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimStampRestart'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Exact stamp history is rebased to memory before P_AimLineAttack setup and retained by the complete source aim call, original return and real miss-to-retry CALL. Concrete next-probe read contracts are reconstructed as before. From that reached retry state, the same authenticated execution runs next ray/setup and path initialization, deriving the incremented epoch and all-false 475-entry visited relation at the actual cell-loop gate; a new exact image starts at next-probe entry memory. This continuation requires explicit initial-word future freshness and successful next-axis divisions. No freshness or stamp image is assumed at a reached intermediate state. Next cell collection, next-route capacity/catalog contracts, reachable invariants and complete three-probe correspondence remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exact stamp history follows full aim entry, real retry and executed next initialization; strict inherited axiom audit.')
if __name__=='__main__':main()

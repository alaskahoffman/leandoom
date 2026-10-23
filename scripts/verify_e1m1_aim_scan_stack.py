#!/usr/bin/env python3
"""Authenticate stack position through common aiming scans and their callers."""
import argparse,json,re,subprocess
import verify_e1m1_aim_saved_caller as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimScanStack':['terminal','callback','dispatch','execution'],
 'E1M1AimActorScanStack':['skipped','top_rejected','bottom_rejected','skipped_position','top_rejected_position','bottom_rejected_position'],
 'E1M1AimLineScanStack':['execution','position'],
 'E1M1AimScanCaller':['exit_stack','execution']}
DISPATCH_ARGS='s hits resolve bounded limit encoded maximum pc targetSafe cursorSafe recordSafe'
HISTORY_ARGS='s f initial work seen visits resolve history bounded counter limit encoded maximum targetSafe cursorSafe recordSafe'
SKIP_ARGS='s f initial work seen visits resolve target sp fraction j selection layout bounded history encoded'
REJECT_ARGS='s f initial work seen visits resolve target sp fraction j history selection layout bounded stable'
ACTOR_POSITION_ARGS='s initial work resolve portals distance z out marked before pointer inside stack'
LINE_ARGS='s f initial hits seen visits resolve target sp fraction j history selection line front back ff fc bf bc h bounded safe returnSafe go stable cursorSafe targetSafe cursorStore recordSafe'
LINE_POSITION_ARGS='s hit line front back ff fc bf bc h returnSafe cursorSafe slotSafe slotMark target out stack'
RETURN_ARGS='initial resolve start finish base steps answer run exit nonnull image position protect first second'
CONTRACTS=[('E1M1AimScanStack','terminal','target base out position distinct exit'),
 ('E1M1AimScanStack','callback','target base out position live'),
 ('E1M1AimScanStack','dispatch',DISPATCH_ARGS),('E1M1AimScanStack','execution',HISTORY_ARGS),
 ('E1M1AimActorScanStack','skipped',SKIP_ARGS),
 ('E1M1AimActorScanStack','top_rejected',REJECT_ARGS),('E1M1AimActorScanStack','bottom_rejected',REJECT_ARGS),
 *[('E1M1AimActorScanStack',n+'_position',ACTOR_POSITION_ARGS) for n in ['skipped','top_rejected','bottom_rejected']],
 ('E1M1AimLineScanStack','execution',LINE_ARGS),('E1M1AimLineScanStack','position',LINE_POSITION_ARGS),
 ('E1M1AimScanCaller','exit_stack','base out position exit'),('E1M1AimScanCaller','execution',RETURN_ARGS)]
PROGRAMS=[('repeatProgram','ExtractedAimRepeat','E1M1AimRepeatProgram'),
 ('skipProgram','ExtractedAimActorSkip','E1M1AimActorSkip'),
 ('topProgram','ExtractedAimActorReject','E1M1AimActorReject'),
 ('bottomProgram','ExtractedAimActorBottom','E1M1AimActorBottom'),
 ('loopProgram','ExtractedAimActorSelect','E1M1AimActorSelect'),
 ('returnProgram','ExtractedAimCompletedReturn','E1M1AimCompletedReturn')]
NAMESPACE='Doom.Verification.ExtractedAimScanStack'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    owners={'program':'E1M1AimRepeatProgram','ReadFrame':'E1M1AimRepeatProgram','Position':'E1M1AimScanStack',
      'Portal':'E1M1AimCatalog','Persistent':'E1M1AimTraversalInvariant','Frame':'E1M1AimHistoryCycle',
      'Selection':'E1M1HistoryDispatch','History':'E1M1SelectionHistory','consume':'E1M1InterceptMark','address':'E1M1MinimumScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimScanCaller\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for local,ns,module in PROGRAMS:
        source+=f'def {local} := Doom.Verification.{ns}.linked\n'
        source+=f'theorem {local}_checked : {local}={module}.program := Doom.Verification.{ns}.linked_checked\n'
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        for local,_,owner in PROGRAMS:
            decl=decl.replace('Doom.Proofs.'+owner+'.program',local).replace(owner+'.program',local)
        source+='namespace '+module+'\n'+decl+' := by\n  '
        for local,_,_ in PROGRAMS:
            if local+' []' in decl:source+='rw ['+local+'_checked] at *\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+local+'_checked' for local,_,_ in PROGRAMS)+'\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".repeatProgram_checked'"
    require(marker in output,'missing scan stack audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.'+local+'_checked' for local,_,_ in PROGRAMS]
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
    out=ROOT/'artifacts/e1m1-aim-scan-stack';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimScanCaller'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Common minimum scan and history dispatch retain parent ESP on exhaustion/range exit and account for the real callback CALL push. Post-callback scans for ignored actors, top/bottom rejects and continuing lines retain this shape; callback destinations are recovered from entry invariants and proved memory frames. Terminal scan shape composes with saved-caller memory and the real return chain without a separate endpoint ESP equality. The enclosing exhaustive mixed-hit loop has not yet been strengthened with this shape: its endpoint ESP premise remains open. No new binary ranges, runtime or semantics changes. Emulator evidence is inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: common scan stack shape, four callback scans and terminal scan return; strict axiom audit.')
if __name__=='__main__':main()

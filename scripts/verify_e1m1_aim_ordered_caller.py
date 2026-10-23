#!/usr/bin/env python3
"""Authenticate the exhaustive mixed-hit loop through the complete aiming return."""
import argparse,json,re,subprocess
import verify_e1m1_aim_scan_stack as previous
import verify_e1m1_aim_actor_cycle as skipped
import verify_e1m1_aim_actor_reject as top
import verify_e1m1_aim_actor_select as bottom
import verify_e1m1_aim_actor_dispatch as actor
import verify_e1m1_aim_actor_catalog as catalog
import verify_e1m1_aim_history_cycle as opened
import verify_e1m1_aim_traversal_invariant as portal
import verify_e1m1_aim_synchronized_cycle as synchronized
import verify_e1m1_aim_line_cycle as line
import verify_e1m1_aim_ordered_memory as hit
import verify_e1m1_aim_saved_caller as saved
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimStackShape':['scan','stopped','terminal','live'],
 'E1M1AimSkippedStack':['execution'],'E1M1AimTopStack':['execution'],
 'E1M1AimBottomStack':['execution'],'E1M1AimActorStack':['execution','catalog'],
 'E1M1AimOpenStack':['execution'],'E1M1AimPortalStack':['execution'],
 'E1M1AimSynchronizedStack':['execution'],'E1M1AimLineStack':['execution'],
 'E1M1AimHitStack':['execution'],'E1M1AimOrderedStack':['execution','initial'],
 'E1M1AimOrderedCaller':['execution']}
LOOP_ARGS=saved.LOOP_ARGS+' base shape'
INITIAL_ARGS=saved.RESULT_ARGS+' base shape'
CALLER_ARGS=saved.RESULT_ARGS.replace(' available watched ',' available base ')+' shape nonnull first second'
CONTRACTS=[
 ('E1M1AimStackShape','scan','base out position'),('E1M1AimStackShape','stopped','base out pc stack'),
 ('E1M1AimStackShape','terminal','base out shape pc'),('E1M1AimStackShape','live','base out shape pc'),
 ('E1M1AimSkippedStack','execution',skipped.EXEC_ARGS),
 ('E1M1AimTopStack','execution',top.CYCLE_ARGS),('E1M1AimBottomStack','execution',bottom.CYCLE_ARGS),
 ('E1M1AimActorStack','execution',actor.EXEC_ARGS),('E1M1AimActorStack','catalog',catalog.EXEC_ARGS),
 ('E1M1AimOpenStack','execution',opened.CYCLE_ARGS+' callback'),
 ('E1M1AimPortalStack','execution',portal.CYCLE_ARGS),
 ('E1M1AimSynchronizedStack','execution',synchronized.CYCLE_ARGS),
 ('E1M1AimLineStack','execution',line.EXEC_ARGS),('E1M1AimHitStack','execution',hit.HIT_ARGS),
 ('E1M1AimOrderedStack','execution',LOOP_ARGS),('E1M1AimOrderedStack','initial',INITIAL_ARGS),
 ('E1M1AimOrderedCaller','execution',CALLER_ARGS)]
PROGRAMS=[('repeatProgram','ExtractedAimRepeat','E1M1AimRepeatProgram'),
 ('skipProgram','ExtractedAimActorSkip','E1M1AimActorSkip'),
 ('topProgram','ExtractedAimActorReject','E1M1AimActorReject'),
 ('bottomProgram','ExtractedAimActorBottom','E1M1AimActorBottom'),
 ('loopProgram','ExtractedAimActorSelect','E1M1AimActorSelect'),
 ('returnProgram','ExtractedAimCompletedReturn','E1M1AimCompletedReturn')]
NAMESPACE='Doom.Verification.ExtractedAimOrderedCaller'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    program={'E1M1AimSkippedStack':'E1M1AimActorSkip','E1M1AimTopStack':'E1M1AimActorReject',
      'E1M1AimBottomStack':'E1M1AimActorBottom','E1M1AimActorStack':'E1M1AimActorSelect',
      'E1M1AimHitStack':'E1M1AimActorSelect','E1M1AimOrderedStack':'E1M1AimActorSelect',
      'E1M1AimOrderedCaller':'E1M1AimActorSelect'}.get(module,'E1M1AimRepeatProgram')
    next_owner={'E1M1AimSkippedStack':'E1M1AimActorSkipCycle','E1M1AimTopStack':'E1M1AimActorRejectCycle',
      'E1M1AimBottomStack':'E1M1AimActorBottomCycle','E1M1AimOpenStack':'E1M1AimHistoryCycle'}.get(module,'E1M1AimTraversalInvariant')
    owners={'program':program,'Shape':'E1M1AimStackShape','Next':next_owner,
      'Outcome':'E1M1AimActorCycle' if module=='E1M1AimActorStack' else 'E1M1AimHitMemory',
      'dispatch':'E1M1AimActorDispatch' if module=='E1M1AimActorStack' else 'E1M1AimLineDispatch',
      'ReadFrame':'E1M1AimRepeatProgram','Position':'E1M1AimPortalPrefix',
      'Portal':'E1M1AimCatalog','Persistent':'E1M1AimTraversalInvariant','Frame':'E1M1AimHistoryCycle',
      'Selection':'E1M1HistoryDispatch','History':'E1M1SelectionHistory','consume':'E1M1InterceptMark','address':'E1M1MinimumScan',
      'Safe':'E1M1AimWall','Catalog':'E1M1AimActorCatalog','Represents':'E1M1AimSourceCatalog',
      'AlignedNext':'E1M1AimSynchronizedCycle','Coverage':'E1M1AimLineCoverage','Arithmetic':'E1M1AimHitOutcome',
      'Boundary':'E1M1AimActorBoundary','Ready':'E1M1AimMixedExit','Available':'E1M1AimOrderedLoop',
      'Exit':'E1M1AimHitMemory','StableWord':'E1M1AimMapFrame'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimOrderedCaller\n'+previous.certificate(data,raw)
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
    require(marker in output,'missing ordered caller audit')
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
    out=ROOT/'artifacts/e1m1-aim-ordered-caller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimOrderedCaller'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Every actor and wall callback preserves saved words and stack shape. The exhaustive mixed-hit loop proves its final parent ESP from an entry shape, and the completed real return uses its derived stack and memory image. The combined execution returns the same production afterPath slope in EAX and restores caller values from entry memory, without endpoint ESP/memory or a future branch sequence. Entry alignment, catalogs, memory protection, nullness, non-null resolver, arithmetic availability and saved return addresses remain premises. Initialization/collection joining and reachable-state equivalence remain open. No new byte ranges, instruction semantics or runtime changes. Emulator evidence is inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exhaustive mixed-hit loop and complete caller return; strict axiom audit.')
if __name__=='__main__':main()

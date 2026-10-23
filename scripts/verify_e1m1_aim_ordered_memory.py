#!/usr/bin/env python3
"""Authenticate null-target preservation and original return-value selection."""
import argparse,json,re,subprocess
import verify_e1m1_aim_ordered_loop as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+"\nopen E1M1AimSourceCatalog (front back)\n"
GROUPS={'E1M1AimNoTargetFrame':['opening_safe','wall','closed'],'E1M1AimLineFrameCycle':['execution'],
 'E1M1AimHitMemory':['no_target_value','return_value','execution'],'E1M1AimOrderedMemory':['execution','initial']}
HIT_ARGS=previous.HIT_ARGS+' null targetSafe'
LOOP_ARGS=previous.LOOP_ARGS+' null'
RESULT_ARGS=previous.RESULT_ARGS+' targetSafe null'
NONE_ARGS='initial resolve out answer exit absent'
RETURN_ARGS='initial resolve out answer exit nonnull'
CONTRACTS=[('E1M1AimHitMemory','execution','hit_checked',HIT_ARGS),
 ('E1M1AimOrderedMemory','execution','loop_checked',LOOP_ARGS),
 ('E1M1AimOrderedMemory','initial','initial_checked',RESULT_ARGS),
 ('E1M1AimHitMemory','no_target_value','none_checked',NONE_ARGS),
 ('E1M1AimHitMemory','return_value','return_checked',RETURN_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    program='E1M1AimRepeatProgram' if module in ['E1M1AimNoTargetFrame','E1M1AimLineFrameCycle'] else 'E1M1AimActorSelect'
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.'+program+'.program',decl)
    owners={'Catalog':'E1M1AimActorCatalog','Entry':'E1M1AimActorCatalog','Inputs':'E1M1AimActorCatalog',
            'Outcome':'E1M1AimHitMemory','Arithmetic':'E1M1AimHitOutcome','Exit':'E1M1AimHitMemory','Available':'E1M1AimOrderedLoop','dispatch':'E1M1AimLineDispatch','Coverage':'E1M1AimLineCoverage','Safe':'E1M1AimWall','Represents':'E1M1AimSourceCatalog',
            'AlignedNext':'E1M1AimSynchronizedCycle','Position':'E1M1AimPortalPrefix','Sequence':'E1M1AimMixedPrefix','Step':'E1M1AimMixedStep','Boundary':'E1M1AimActorBoundary','Ready':'E1M1AimMixedExit','Frame':'E1M1AimHistoryCycle','advance':'E1M1AimPortalPrefix',
            'minimum':'E1M1InterceptMinimum','StableWord':'E1M1AimMapFrame','address':'E1M1MinimumScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimOrderedMemory\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimOrderedMemory\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '+('rw [linked_checked]\n  ' if 'linked []' in decl else '')+'exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimOrderedMemory\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimOrderedMemory.linked_checked'"
    require(marker in output,'missing ordered memory audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimOrderedMemory.linked_checked']
    names+=['Doom.Verification.ExtractedAimOrderedMemory.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    parser=argparse.ArgumentParser();parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-ordered-memory';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimOrderedMemory'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Stopping and continuing lines retain a proved word frame. The exhaustive ordered loop now preserves '
      'an initially null target on every no-target outcome and retains exact selected target/slope stores. '
      'The original return-value selection produces zero for a null target regardless of stale slope memory, '
      'and equals the source slope for all outcomes under an explicit non-null resolver premise. '
      'Initial nullness/protection, representation, coverage and uniform arithmetic availability remain premises; '
      'collection-to-boundary preservation and execution through the traversal/aiming epilogues remain open. '
      'No new binary ranges, runtime or instruction-semantics changes. Emulator evidence is inherited.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: null-target preservation and return-value selection; strict axiom audit.')
if __name__=='__main__':main()

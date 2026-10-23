#!/usr/bin/env python3
"""Authenticate exhaustive ordered-hit dispatch and bounded termination."""
import argparse,json,re,subprocess
import verify_e1m1_aim_mixed_exit as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+"\nopen E1M1AimSourceCatalog (front back)\n"
GROUPS={'E1M1AimHitOutcome':['execution'],'E1M1AimOrderedLoop':['execution'],'E1M1AimOrderedResult':['execution']}
COMMON_ARGS='scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query'
HIT_ARGS=COMMON_ARGS+' a s f seen visits sp fraction j history selection before bottom top actors wallCatalog arithmetic'
LOOP_ARGS=COMMON_ARGS+' available fuel a origin s seen visits budget history boundary bottom top ready'
RESULT_ARGS=COMMON_ARGS+' available origin s aligned bottom top actors wallCatalog'
CONTRACTS=[('E1M1AimHitOutcome','execution','hit_checked',HIT_ARGS),
 ('E1M1AimOrderedLoop','execution','loop_checked',LOOP_ARGS),
 ('E1M1AimOrderedResult','execution','result_checked',RESULT_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.E1M1AimActorSelect.program',decl)
    owners={'Catalog':'E1M1AimActorCatalog','Entry':'E1M1AimActorCatalog','Inputs':'E1M1AimActorCatalog',
            'Outcome':'E1M1AimHitOutcome','Arithmetic':'E1M1AimHitOutcome','Exit':'E1M1AimHitOutcome','Available':'E1M1AimOrderedLoop','dispatch':'E1M1AimActorDispatch','Represents':'E1M1AimSourceCatalog',
            'AlignedNext':'E1M1AimSynchronizedCycle','Position':'E1M1AimPortalPrefix','Sequence':'E1M1AimMixedPrefix','Step':'E1M1AimMixedStep','Boundary':'E1M1AimActorBoundary','Ready':'E1M1AimMixedExit','Frame':'E1M1AimHistoryCycle','advance':'E1M1AimPortalPrefix',
            'minimum':'E1M1InterceptMinimum','StableWord':'E1M1AimMapFrame','address':'E1M1MinimumScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimOrderedResult\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimOrderedLoop\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '+('rw [linked_checked]\n  ' if 'linked []' in decl else '')+'exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimOrderedLoop\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimOrderedLoop.linked_checked'"
    require(marker in output,'missing ordered loop audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimOrderedLoop.linked_checked']
    names+=['Doom.Verification.ExtractedAimOrderedLoop.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    out=ROOT/'artifacts/e1m1-aim-ordered-loop';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimOrderedResult'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='An exhaustive callback theorem derives all line/actor stop and continuation cases. '
      'Strong induction on remaining distinct records proves bounded execution to a real DOS traversal exit, '
      'without a source Sequence or supplied final branch. The initial-boundary wrapper matches the production afterPath result '
      'and, for selected targets, the exact target/slope stores. '
      'Premises include coverage, initial boundary/catalogs, and uniform arithmetic availability over admitted histories/windows; '
      'that arithmetic premise is stronger than availability only on one actual reachable trace. '
      'Reachable initialization, no-target global clearing/preservation, traversal epilogue and enclosing aiming returns remain open. '
      'No new binary ranges, runtime or instruction-semantics changes. Emulator evidence is inherited.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exhaustive ordered loop and bounded termination; strict axiom audit.')
if __name__=='__main__':main()

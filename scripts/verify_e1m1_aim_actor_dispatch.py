#!/usr/bin/env python3
"""Authenticate unified actor dispatch and shared continuation boundaries."""
import argparse,json,re,subprocess
import verify_e1m1_aim_actor_return as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimActorBoundary': ['exhausted_pc', 'skipped', 'top_rejected', 'bottom_rejected', 'next_callback', 'line_boundary'], 'E1M1AimActorDispatch': ['ignored', 'eligible', 'equality'], 'E1M1AimActorCycle': ['contains_reject', 'contains_skip', 'execution']}
EXEC_ARGS=previous.STOP_ARGS.replace(' different shootable','').replace('topOk admitted bottomOk bottomAdmitted','topOk bottomOk')
NEXT_ARGS='s scene shooter thing path original distance work seen visits resolve portals lower upper log out history empty query boundary fraction j chosen within'
CONTRACTS=[('E1M1AimActorCycle','execution','cycle_checked',EXEC_ARGS),
 ('E1M1AimActorBoundary','line_boundary','line_checked',NEXT_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.E1M1AimActorSelect.program',decl)
    owners={'Safe':'E1M1AimWall','Outcome':'E1M1AimActorCycle','dispatch':'E1M1AimActorDispatch',
            'Decision':'E1M1AimActorDispatch','Boundary':'E1M1AimActorBoundary'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimActorCycle\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimActorDispatch\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '+('rw [linked_checked]\n  ' if 'linked []' in decl else '')+'exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimActorDispatch\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimActorDispatch.linked_checked'"
    require(marker in output,'missing actor return audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimActorDispatch.linked_checked']
    names+=['Doom.Verification.ExtractedAimActorDispatch.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def cross_check(spec,raw,count=384):
    import verify_e1m1_aim_actor_skip as skip
    import verify_e1m1_aim_actor_reject as rejected
    results=dict(ignored=skip.cross_check(raw,count),top_rejected=rejected.cross_check(spec,raw,count),
                 bottom_and_selection=previous.cross_check(spec,raw,count))
    return dict(cases=3*count,suites=results,
                scope='Fresh regression execution of the existing authenticated branch suites: ignored actors through parent mark, top rejection through next scan, and both bottom outcomes through scan or selected return/stop. Universal dispatch and common-boundary composition are established by the new Lean theorem, not by sampling.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-actor-dispatch';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimActorCycle'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='One authenticated actor-cycle theorem dispatches ignored actors, rejected tops, rejected bottoms and selected actors in source order. '
      'Divisions are required only on reached branches. Continuing outcomes share a terminal-or-aligned-callback interface and preserve source progress, bounds, portal log, frame and selection stack separation. '
      'Selected actors preserve the unmarked buffer and return the exact source target/slope/window/path at the parent stop. '
      'The shared next callback can feed the existing line/portal interface. '
      'Actor representation/catalog persistence, arbitrary mixed-loop composition, enclosing returns and whole aiming remain open. No runtime or semantics changes.')
    if args.cross_check:report['cross_check']=cross_check(spec,raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: unified actor dispatch and common next-hit interface; strict axiom audit.')
if __name__=='__main__':main()

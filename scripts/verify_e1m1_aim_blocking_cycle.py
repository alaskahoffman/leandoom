#!/usr/bin/env python3
"""Authenticate selected one-sided and closed-opening aiming stops."""
import argparse,json,re,subprocess
import verify_e1m1_aim_portal_prefix as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimBlockingSource':['wall','closed'],
 'E1M1AimClosedReturn':['contains_opening','contains_guard','stop_fields','return_frame','execution','frame'],
 'E1M1AimBlockingCycle':['wall_execution','prologue_safe','wall','closed']}
WALL_ARGS='s f scene shooter thing path result work seen visits resolve distance target sp fraction j history selection layout empty query lower upper log bottom top isLine flagsSafe flags solid'
CLOSED_ARGS='s f scene shooter thing path result work seen visits resolve portals distance target sp fraction j p history selection before represented listed empty query lower upper log bottom top blocked'
RETURN_ARGS='s f hit line front back ff fc bf bc h safe returnWord closed'
CONTRACTS=[('E1M1AimClosedReturn','execution','return_checked',RETURN_ARGS),('E1M1AimBlockingCycle','wall','wall_checked',WALL_ARGS),('E1M1AimBlockingCycle','closed','closed_checked',CLOSED_ARGS)]


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimBlockingCycle\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimBlockingCycle\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1InterceptMark (consume)\nopen E1M1AimCatalog (Portal)\nopen E1M1AimTraversalInvariant (Persistent Next)\nopen E1M1AimSourceCatalog (Represents front back)\nopen E1M1AimIteration\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimRepeatProgram (program)\nopen E1M1AimSynchronizedCycle (AlignedNext)\nopen E1M1AimWall (Safe)\nopen E1M1InterceptMinimum (minimum)\n'
    for module,name,checked,args in CONTRACTS:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        decl=re.sub(r'\bprogram\b','Doom.Proofs.E1M1AimRepeatProgram.program',decl)
        if module=='E1M1AimClosedReturn':decl=decl.replace('(result s)', '(Doom.Proofs.E1M1AimClosedReturn.result s)')
        source+='namespace '+module+'\n'+decl+' := Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimBlockingCycle\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimBlockingCycle.E1M1AimClosedReturn.return_checked'"
    require(marker in output,'missing blocking cycle audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimBlockingCycle.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


cross_check=previous.cross_check

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-blocking-cycle';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimBlockingCycle'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='One-sided walls and closed two-sided openings at an actual selected callback stop the original binary and canonical production suffix on the same hit. '
      'Closed openings execute through RET and the parent false branch; both joins preserve clipping bounds and exact stop visit counts. '
      'The shared repeat program and reached history/selection boundary are reused. Wall flags and separation remain explicit premises, not a preserved wall catalog. '
      'Complete line classification, prefix integration, actors, complete-query coverage and reachable-state premise discharge remain open. No complete aiming or whole-game equivalence claim. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: selected one-sided and closed-opening stops; strict axiom audit.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Authenticate finite portal-prefix induction and its original traversal exits."""
import argparse,json,re,subprocess
import verify_e1m1_aim_synchronized_cycle as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimPortalPrefix':['seed','execution','capacity'],
 'E1M1AimPortalPrefixExit':['terminal','completed','stopped']}
EXEC_ARGS='scene shooter thing path result distance resolve portals represented empty query a final count sequence origin s seen visits history aligned bottom top'
COMPLETE_ARGS=EXEC_ARGS+' done'
STOP_ARGS=EXEC_ARGS+' fraction j p floorSlope ceilingSlope chosen within listed pass floorOk ceilingOk closed'


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimPortalPrefixExit\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimPortalPrefix\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1InterceptMark (consume)\nopen E1M1AimCatalog (Portal)\nopen E1M1AimTraversalInvariant (Persistent Next)\nopen E1M1AimSourceCatalog (Represents front back)\nopen E1M1AimIteration\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimRepeatProgram (program)\nopen E1M1AimSynchronizedCycle (AlignedNext)\nopen E1M1AimPortalPrefix (Position advance Sequence)\nopen E1M1InterceptMinimum (minimum)\n'
    for module,name,checked,args in [('E1M1AimPortalPrefix','execution','prefix_checked',EXEC_ARGS),('E1M1AimPortalPrefixExit','completed','complete_checked',COMPLETE_ARGS),('E1M1AimPortalPrefixExit','stopped','stop_checked',STOP_ARGS)]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['prefix_checked','complete_checked','stop_checked'])+'\nend Doom.Verification.ExtractedAimPortalPrefix\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimPortalPrefix.prefix_checked'"
    require(marker in output,'missing portal prefix audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimPortalPrefix.'+n for n in ['prefix_checked','complete_checked','stop_checked']]
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
    out=ROOT/'artifacts/e1m1-aim-portal-prefix';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimPortalPrefixExit'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Induction over any finite certified sequence of continuing source portal branches derives all later original selections, invariant states and clipping bounds from one initial boundary. '
      'The actual instruction prefixes compose, the canonical source suffix agrees, and distinct-history capacity bounds progress. '
      'Normal exhaustion/range exits and a later callback closing the window compose with the whole prefix, retaining exact original PCs and source visit counts. '
      'Sequence certificates contain only source selection/branch/arithmetic facts, not machine states or callback conclusions. '
      'Other line/actor branches, generating complete-query coverage, query initialization and reachable-state premise discharge remain open. No full aiming or whole-game equivalence claim. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: finite original portal-prefix induction and normal/stopped exits; strict axiom audit.')
if __name__=='__main__':main()

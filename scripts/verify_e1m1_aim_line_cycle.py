#!/usr/bin/env python3
"""Authenticate unified selected-line dispatch against the DOS callback."""
import argparse,json,re,subprocess
import verify_e1m1_aim_blocking_prefix as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimLineDispatch':['wall','closed','opened'],
 'E1M1AimLineCoverage':['selected','exclusive'],
 'E1M1AimLineCycle':['execution']}
SELECT_ARGS='initial work seen resolve walls portals target sp s fraction j selection covered isLine'
EXCLUSIVE_ARGS='scene initial walls portals j p inside wallMap portalMap wall listed'
EXEC_ARGS='s f scene shooter thing path result work seen visits resolve portals walls distance target sp fraction j history selection before represented catalog wallMap covered isLine empty query lower upper floorSlope ceilingSlope log bottom top divisions'
CONTRACTS=[('E1M1AimLineCoverage','selected','selected_checked',SELECT_ARGS),('E1M1AimLineCoverage','exclusive','exclusive_checked',EXCLUSIVE_ARGS),('E1M1AimLineCycle','execution','dispatch_checked',EXEC_ARGS)]


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimLineCycle\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimLineCycle\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1InterceptMark (consume)\nopen E1M1AimCatalog (Portal)\nopen E1M1AimTraversalInvariant (Persistent Next)\nopen E1M1AimSourceCatalog (Represents front back)\nopen E1M1AimIteration\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimRepeatProgram (program)\nopen E1M1AimSynchronizedCycle (AlignedNext)\nopen E1M1AimWall (Safe)\nopen E1M1AimLineDispatch (dispatch)\nopen E1M1AimLineCoverage (Coverage)\nopen E1M1MinimumScan (address)\nopen E1M1AimPortalPrefix (Position advance Sequence)\nopen E1M1InterceptMinimum (minimum)\n'
    for module,name,checked,args in CONTRACTS:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        decl=re.sub(r'\bprogram\b','Doom.Proofs.E1M1AimRepeatProgram.program',decl)
        source+='namespace '+module+'\n'+decl+' := Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimLineCycle\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimLineCycle.E1M1AimLineCoverage.selected_checked'"
    require(marker in output,'missing line dispatch audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimLineCycle.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    out=ROOT/'artifacts/e1m1-aim-line-cycle';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimLineCycle'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='One selected-line theorem follows source flags, signed opening bounds and aim-window clipping to cover walls, closed openings, window-closing portals and continuing portals. '
      'Branch outcomes are derived from catalog coverage and source representation; guarded division success remains an explicit arithmetic premise. '
      'Each outcome composes actual DOS instructions with the canonical production suffix. Continuing callbacks preserve wall data for reuse. '
      'Missing back sectors are rejected, actors remain outside line coverage, and source representations prohibit conflicting wall/portal labels. '
      'This completes the local covered-line dispatch interface, not arbitrary-query or whole-aiming equivalence. Actor processing, mixed-loop/call/controller composition and reachable-state premise discharge remain open. No runtime changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: unified covered-line dispatch; strict axiom audit.')
if __name__=='__main__':main()

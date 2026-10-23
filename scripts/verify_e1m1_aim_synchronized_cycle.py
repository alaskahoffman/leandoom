#!/usr/bin/env python3
"""Authenticate the synchronized source/DOS open-portal cycle."""
import argparse,json,re,subprocess
import verify_e1m1_aim_path_bridge as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimSourceCatalog':['entry','arithmetic'],
 'E1M1AimSynchronizedCycle':['indices','boundary','next_callback','execution']}
NEXT_ARGS='s scene shooter thing path result distance work seen visits resolve portals lower upper log out history empty query aligned fraction j chosen within'
CYCLE_ARGS='s f scene shooter thing path result work seen visits resolve portals distance target sp fraction j p history selection before represented listed empty query lower upper floorSlope ceilingSlope log bottom top pass floorOk ceilingOk'


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimSynchronizedCycle\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimSynchronizedCycle\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1InterceptMark (consume)\nopen E1M1AimCatalog (Portal)\nopen E1M1AimTraversalInvariant (Persistent Next)\nopen E1M1AimSourceCatalog (Represents front back)\nopen E1M1AimIteration\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimRepeatProgram (program)\nopen E1M1AimSynchronizedCycle (AlignedNext)\n'
    for module,name,checked,args in [('E1M1AimSynchronizedCycle','next_callback','next_checked',NEXT_ARGS),('E1M1AimSynchronizedCycle','execution','cycle_checked',CYCLE_ARGS)]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['next_checked','cycle_checked'])+'\nend Doom.Verification.ExtractedAimSynchronizedCycle\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimSynchronizedCycle.next_checked'"
    require(marker in output,'missing synchronized cycle audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimSynchronizedCycle.'+n for n in ['next_checked','cycle_checked']]
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
    out=ROOT/'artifacts/e1m1-aim-synchronized-cycle';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSynchronizedCycle'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='A shared immutable scene/catalog representation converts source heights and conditional division premises to the original binary contract. '
      'One authentic callback/return/mark/rescan cycle is joined to the canonical source aiming suffix, with identical clipped bounds and stop/continue condition. '
      'The next boundary carries a finished source suffix or its reached selected hit and persistent invariant. An admitted next hit rules out terminal boundaries. '
      'The shared collection, query output, source/catalog relation and initial invariant remain premises; selected open two-sided lines and successful conditional divisions are required. '
      'Repeated-loop induction, query-entry establishment, other callback branches and reachable-state division discharge remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: synchronized production portal cycle and reusable next callback; strict axiom audit.')
if __name__=='__main__':main()

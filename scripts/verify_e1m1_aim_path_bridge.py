#!/usr/bin/env python3
"""Authenticate the production aim-path ordering and DOS selection bridge."""
import argparse,json,re,subprocess
import verify_e1m1_aim_traversal_invariant as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimPathOrder':['replay','suffix','next_hit','terminal'],
 'E1M1AimPathBridge':['selected','next_line','finished']}
SELECT_ARGS='result path work seen visits resolve target sp s fraction j history selection empty run'
LINE_ARGS='scene shooter thing path distance rest lower upper floorSlope ceilingSlope portals back result work seen visits resolve target sp s fraction j history selection empty run isLine two backSector pass floorOk ceilingOk'
FINISH_ARGS='scene shooter thing path result distance lower upper portals work seen visits history empty done run'


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimPathBridge\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimPathBridge\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1AimIteration E1M1AimSource\n'
    for module,name,checked,args in [('E1M1AimPathBridge','selected','selection_checked',SELECT_ARGS),('E1M1AimPathBridge','next_line','line_checked',LINE_ARGS),('E1M1AimPathBridge','finished','finish_checked',FINISH_ARGS)]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['selection_checked','line_checked','finish_checked'])+'\nend Doom.Verification.ExtractedAimPathBridge\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimPathBridge.selection_checked'"
    require(marker in output,'missing path bridge audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimPathBridge.'+n for n in ['selection_checked','line_checked','finish_checked']]
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
    out=ROOT/'artifacts/e1m1-aim-path-bridge';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimPathBridge'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Every admitted selection history replays to the exact suffix of the production all-accepting visitor. '
      'The reached DOS selection is proved to be the next original hit in the precomputed source path, including strict-min ties. '
      'The source open-line step now derives hit identity, and exhausted/range exits imply an empty source aim suffix. '
      'Same initial collection, empty initial visits, and the successful production visitHits result remain explicit premises; '
      'joining collection/query entry, persistent-invariant initialization, other callback branches, checked division discharge and full loop induction remain open. '
      'No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: production aim-path order, DOS selection and source suffix bridge; strict axiom audit.')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Authenticate the persistent aiming catalog and reusable cycle invariant."""
import argparse,json,re,subprocess
import verify_e1m1_aim_next_line as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimCatalog':['entry_frame','preserved','inputs'],
 'E1M1AimTraversalInvariant':['bounds_mark','preserved','carried','execution']}
PRESERVE_ARGS='s initial work marked seen visits resolve portals distance z target out fraction j history selection before frame pointer inside'
CYCLE_ARGS='s f initial work seen visits resolve portals distance z target sp fraction j p history selection before listed lower upper floorSlope ceilingSlope bottom top pass floorOk ceilingOk'


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimTraversalInvariant\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimTraversalInvariant\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory E1M1InterceptMinimum\nopen E1M1AimNextSelection (head)\nopen E1M1MinimumScan (address)\nopen E1M1AimRepeatProgram (program ReadFrame)\nopen E1M1OrderedTraversal (appended)\nopen E1M1OrderedVisit (walk)\nopen E1M1InterceptMark (consume)\nopen E1M1HistoryDispatch (Selection)\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimCycleInvariant (Layout QuerySafe)\nopen E1M1AimMapFrame (StableWord Region)\nopen E1M1AimNextLine (ClipGlobalsSafe)\nopen E1M1AimCatalog (Portal Catalog)\nopen E1M1AimTraversalInvariant (Persistent Next)\n'
    for module,name,checked,args in [('E1M1AimTraversalInvariant','preserved','invariant_checked',PRESERVE_ARGS),('E1M1AimTraversalInvariant','execution','cycle_checked',CYCLE_ARGS)]:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        source+=decl+' := '+module+'.'+name+' '+args+'\n'
    source+='\n'.join('#print axioms '+n for n in ['invariant_checked','cycle_checked'])+'\nend Doom.Verification.ExtractedAimTraversalInvariant\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimTraversalInvariant.invariant_checked'"
    require(marker in output,'missing traversal invariant audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimTraversalInvariant.'+n for n in ['invariant_checked','cycle_checked']]
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
    out=ROOT/'artifacts/e1m1-aim-traversal-invariant';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimTraversalInvariant'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='A persistent catalog preserves all represented two-sided lines simultaneously. '
      'The complete open-line callback/selection cycle derives its entry inputs from that catalog and returns the whole persistent invariant at the next reached callback, including the original callback slot and query words. '
      'Catalog initialization, uncatalogued/other callback branches, conditional divisions, full loop induction and precomputed source aim-suffix alignment remain open. No runtime or decoder changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: persistent catalog and closed next-callback invariant; strict axiom audit.')
if __name__=='__main__':main()

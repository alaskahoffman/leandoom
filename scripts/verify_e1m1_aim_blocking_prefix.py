#!/usr/bin/env python3
"""Authenticate finite prefixes ending at walls or closed openings."""
import argparse,json,re,subprocess
import verify_e1m1_aim_blocking_cycle as previous
ROOT,require=previous.ROOT,previous.require
pinned_data=previous.pinned_data
extracted=previous.extracted
GROUPS={
 'E1M1AimWallCatalog':['preserved','inputs'],
 'E1M1AimPortalCarry':['next_choice','execution'],
 'E1M1AimBlockingPrefix':['closed','wall']}
BASE_ARGS='scene shooter thing path result distance resolve portals represented empty query a final count sequence origin s seen visits history aligned bottom top'
PRESERVE_ARGS='s out marked initial resolve walls frame stack pointer bounded catalog'
CARRY_ARGS=BASE_ARGS+' Carry preserve carried fraction j chosen within'
CLOSED_ARGS=BASE_ARGS+' fraction j p chosen within listed blocked'
WALL_ARGS=BASE_ARGS+' walls catalog wallMap fraction j chosen within listed'
CONTRACTS=[('E1M1AimWallCatalog','preserved','preserve_checked',PRESERVE_ARGS),('E1M1AimPortalCarry','execution','carry_checked',CARRY_ARGS),('E1M1AimBlockingPrefix','closed','closed_checked',CLOSED_ARGS),('E1M1AimBlockingPrefix','wall','wall_checked',WALL_ARGS)]


def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimBlockingPrefix\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimBlockingPrefix\nset_option backward.isDefEq.respectTransparency false\nopen Doom Doom.Proofs X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory\nopen E1M1HistoryDispatch (Selection)\nopen E1M1InterceptMark (consume)\nopen E1M1AimCatalog (Portal)\nopen E1M1AimTraversalInvariant (Persistent Next)\nopen E1M1AimSourceCatalog (Represents front back)\nopen E1M1AimIteration\nopen E1M1AimHistoryCycle (Frame)\nopen E1M1AimRepeatProgram (program)\nopen E1M1AimSynchronizedCycle (AlignedNext)\nopen E1M1AimWall (Safe)\nopen E1M1MinimumScan (address)\nopen E1M1AimPortalPrefix (Position advance Sequence)\nopen E1M1InterceptMinimum (minimum)\n'
    for module,name,checked,args in CONTRACTS:
        text=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=text.index('theorem '+name+' ')
        decl=text[a:text.index(' := by',a)].replace('theorem '+name,'theorem '+checked,1)
        decl=re.sub(r'\bprogram\b','Doom.Proofs.E1M1AimRepeatProgram.program',decl)
        if module=='E1M1AimWallCatalog':decl=re.sub(r'\bCatalog\b','Doom.Proofs.E1M1AimWallCatalog.Catalog',decl)
        source+='namespace '+module+'\n'+decl+' := Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimBlockingPrefix\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimBlockingPrefix.E1M1AimWallCatalog.preserve_checked'"
    require(marker in output,'missing blocking prefix audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimBlockingPrefix.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    out=ROOT/'artifacts/e1m1-aim-blocking-prefix';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimBlockingPrefix'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='An initial partial wall catalog is preserved across continuing callbacks using the existing memory frame. '
      'A generic carry induction derives protected properties and the final selected callback through a finite portal prefix. '
      'Whole-prefix wall and closed-opening endings execute original instructions to 0x2c88c, preserve the final portal bounds, and stop the canonical source result at seen+count+1. '
      'No final-state wall flags, selection or invariant are supplied. Source sequence, initial representations and final source branch remain explicit premises. '
      'Unified line classification, actors, complete query/controller composition and reachable-state premise discharge remain open. No full aiming or game equivalence. No runtime changes.')
    if args.cross_check:report['cross_check']=cross_check(raw)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: carried wall catalog and whole-prefix blocking endings; strict axiom audit.')
if __name__=='__main__':main()

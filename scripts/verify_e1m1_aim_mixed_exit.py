#!/usr/bin/env python3
"""Authenticate mixed traversal exhaustion and blocking exits."""
import argparse,json,re,subprocess
import verify_e1m1_aim_mixed_traversal as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+"\nopen E1M1AimSourceCatalog (front back)\n"
GROUPS={'E1M1AimMixedBoundary':['from_line','execution'],
        'E1M1AimMixedExit':['execution','completed'],'E1M1AimMixedBlocking':['closed','stopped','wall']}
STEP_ARGS=previous.STEP_ARGS.replace(' nextFraction k chosen within','')
COMMON_ARGS='scene shooter thing path original distance resolve portals who represented empty query a final count sequence origin s seen visits history aligned bottom top'
EXEC_ARGS=COMMON_ARGS.replace(' aligned ',' boundary ')+' Carry preserve ready'
DONE_ARGS=COMMON_ARGS+' catalog done'
BLOCK_COMMON=COMMON_ARGS.replace(' original ',' result ')+' actors'
CLOSED_ARGS=BLOCK_COMMON+' fraction j p chosen within listed blocked'
STOP_ARGS=BLOCK_COMMON+' fraction j p floorSlope ceilingSlope chosen within listed pass floorOk ceilingOk closed'
WALL_ARGS=BLOCK_COMMON+' walls catalog wallMap fraction j chosen within listed'
CONTRACTS=[('E1M1AimMixedBoundary','execution','step_checked',STEP_ARGS),
 ('E1M1AimMixedExit','execution','prefix_checked',EXEC_ARGS),
 ('E1M1AimMixedExit','completed','completed_checked',DONE_ARGS),
 ('E1M1AimMixedBlocking','closed','closed_checked',CLOSED_ARGS),
 ('E1M1AimMixedBlocking','stopped','stopped_checked',STOP_ARGS),
 ('E1M1AimMixedBlocking','wall','wall_checked',WALL_ARGS)]

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:source.index(' := by',a)]
    decl=re.sub(r'(?<![.\w])program\b','Doom.Proofs.E1M1AimActorSelect.program',decl)
    owners={'Catalog':'E1M1AimActorCatalog','Entry':'E1M1AimActorCatalog','Inputs':'E1M1AimActorCatalog',
            'Outcome':'E1M1AimActorCycle','dispatch':'E1M1AimActorDispatch','Represents':'E1M1AimSourceCatalog',
            'AlignedNext':'E1M1AimSynchronizedCycle','Position':'E1M1AimPortalPrefix','Sequence':'E1M1AimMixedPrefix','Step':'E1M1AimMixedStep','Boundary':'E1M1AimActorBoundary','Ready':'E1M1AimMixedExit','Frame':'E1M1AimHistoryCycle','advance':'E1M1AimPortalPrefix',
            'minimum':'E1M1InterceptMinimum','StableWord':'E1M1AimMapFrame','address':'E1M1MinimumScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b',lambda m:'Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimMixedBlocking\n'+previous.certificate(data,raw)
    source+='\nnamespace Doom.Verification.ExtractedAimMixedExit\n'+HEADER
    source+='def linked := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem linked_checked : linked=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '+('rw [linked_checked]\n  ' if 'linked []' in decl else '')+'exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend Doom.Verification.ExtractedAimMixedExit\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'Doom.Verification.ExtractedAimMixedExit.linked_checked'"
    require(marker in output,'missing mixed exit audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=['Doom.Verification.ExtractedAimMixedExit.linked_checked']
    names+=['Doom.Verification.ExtractedAimMixedExit.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    out=ROOT/'artifacts/e1m1-aim-mixed-exit';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimMixedBlocking'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Mixed continuing sequences no longer require an admitted final hit. They retain the actual DOS normal-exit '
      'or live-callback boundary. Exhaustion and range rejection reach PC 0x2c887 and the canonical source no-target result. '
      'Closed sectors, a closed clipped window, or a represented wall after a mixed prefix reach PC 0x2c88c and the exact stopped source path. '
      'Generic frame-preserved data is carried only at live callbacks, including the wall catalog. '
      'These remain conditional on source sequence/branch premises and initial representation. '
      'Total branch classification, reachable initialization and enclosing returns remain open. '
      'No new binary ranges, runtime or instruction-semantics changes. Emulator evidence is inherited.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: mixed exhaustion and blocking exits; strict axiom audit.')
if __name__=='__main__':main()

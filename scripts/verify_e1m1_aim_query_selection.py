#!/usr/bin/env python3
"""Authenticate query initialization/collection through the first ordered aim hit."""
import argparse,json,re,subprocess
import verify_e1m1_aim_ordered_caller as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'''
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1QueryCallback (CallbackSafe)
'''
GROUPS={
 'E1M1ScanInterface':['dispatch'],
 'E1M1AimEntryFrame':['return_word','return_safe','preserved'],
 'E1M1AimFirstSelection':['execution','source'],
 'E1M1AimQuerySelection':['execution']}
CONTRACTS=[
 ('E1M1ScanInterface','dispatch','program contains_selection contains_call s hits resolve bounded limit encoded maximum pc targetSafe cursorSafe recordSafe'),
 ('E1M1AimEntryFrame','return_word','s n'),
 ('E1M1AimEntryFrame','return_safe','sp'),
 ('E1M1AimEntryFrame','preserved','s n out frame a safe stack'),
 ('E1M1AimFirstSelection','execution','s f hits resolve bounded limit encoded protect callback'),
 ('E1M1AimFirstSelection','source','original path resolve base out outcome empty query'),
 ('E1M1AimQuerySelection','execution','q pick s f sx sy ex ey entry profile xout yout okX okY common height statics scenes payloads separated callbackSafe argument cursorCall room')]
NAMESPACE='Doom.Verification.ExtractedAimQuerySelection'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'result':'E1M1InterceptSetup','ReadFrame':'E1M1AimRepeatProgram',
      'SafeWord':'E1M1AimEntryFrame','Position':'E1M1AimScanStack','address':'E1M1MinimumScan',
      'Outcome':'E1M1AimFirstSelection','Protected':'E1M1AimFirstSelection' if module=='E1M1AimFirstSelection' else 'E1M1TraversalEntry'}
    if module!='E1M1ScanInterface':owners['program']='E1M1FirstIntercept'
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimQuerySelection\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='''
def queryProgram := Doom.Verification.ExtractedQueryDispatch.linked
theorem queryProgram_checked : queryProgram=E1M1FirstIntercept.program :=
  Doom.Verification.ExtractedQueryDispatch.program_checked
'''
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('Doom.Proofs.E1M1FirstIntercept.program','queryProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'queryProgram []' in decl:source+='rw [queryProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms queryProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".queryProgram_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.queryProgram_checked']
    names+=[NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]
    names+=['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]
    for full in names:
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();require(mp['exe_sha256']==profile['exe_sha256'],'profile mismatch')
    out=ROOT/'artifacts/e1m1-aim-query-selection';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimOrderedCaller','Doom.Proofs.E1M1AimQuerySelection'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous path-query initialization, collection, handoff and first ordered selection. Derived empty/far/live alternatives, initial Selection, stack shape, authentic first saved return, and separated-word image from query-entry memory. Source first-hit alignment is proved given an empty collection visitation log and successful all-true source query. Existing initial geometry, map/object, capacity, memory separation and callback argument premises remain. Full persistent catalog transfer into the exhaustive mixed-hit/return theorem, complete aiming and reachable E1M1 states are not closed. No new byte ranges, instruction semantics or runtime changes. Emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: query through first ordered aiming selection; strict axiom audit.')
if __name__=='__main__':main()

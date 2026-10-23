#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_cell_collection as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimCallbackRegions': ['stack_word', 'global_stack', 'stack_array', 'stack_stamps', 'above', 'upper_collection', 'selection', 'initial', 'callback'], 'E1M1AimCallbackEntry': ['pre_ray', 'execution', 'decision']}
CONTRACTS=[('E1M1AimCallbackRegions', 'stack_word', 'stack sp n reserve low high'), ('E1M1AimCallbackRegions', 'global_stack', 'stack sp lines a n placement reserve inside low high'), ('E1M1AimCallbackRegions', 'stack_array', 'stack sp lines n placement reserve low high'), ('E1M1AimCallbackRegions', 'stack_stamps', 'stack sp lines n placement reserve low high'), ('E1M1AimCallbackRegions', 'above', 'sp n off low high deeper'), ('E1M1AimCallbackRegions', 'upper_collection', 'stack sp lines n placement reserve low high'), ('E1M1AimCallbackRegions', 'selection', 'stack q placement reserve'), ('E1M1AimCallbackRegions', 'initial', 'stack q s placement reserve position'), ('E1M1AimCallbackRegions', 'callback', 'stack q s placement reserve position'), ('E1M1AimCallbackEntry', 'pre_ray', 'stack q s placement reserve position'), ('E1M1AimCallbackEntry', 'execution', 'q stack pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes payloads placement reserve room portals walls who initial'), ('E1M1AimCallbackEntry', 'decision', 'q stack pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes payloads placement reserve room portals walls who initial second returnSafe resume')]
NAMESPACE='Doom.Verification.ExtractedAimCallbackEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Layout':'E1M1AimCallbackRegions',
      'CallbackSafe':'E1M1QueryCallback','Source':'E1M1AimQueryCaller',
      'traversal':'E1M1PathMapQuery','resolve':'E1M1ThingFinish'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimCallbackEntry\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='''
/-- Instantiate the new input constructor with the authenticated WAD word array. -/
theorem pinned_map_checked (stack : Region) (s : X86Memory.State) (base lines : Word)
    (reserve : E1M1AimSetupFootprint.Reserve stack s)
    (placement : E1M1AimMapRegions.Layout stack base)
    (values : E1M1AimMapEntry.Values s.memory base lines Doom.Verification.ExtractedPathMap.words) :
    E1M1PathMapQuery.MapInputs s base lines Doom.Verification.ExtractedPathMap.words 36 23 := by
  exact E1M1AimMapEntry.inputs stack s base lines _ reserve placement
    Doom.Verification.ExtractedPathMap.shape_checked.1 values
'''
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        source+='namespace '+module+'\n'+decl+' := by\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms pinned_map_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".pinned_map_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.pinned_map_checked']
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
    out=ROOT/'artifacts/e1m1-aim-callback-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimCallbackEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Derive traversal prologue record/cursor protection, saved callback-pointer protection through path setup and collection, and final callback CALL protection from a nonwrapping 212-byte stack reserve and separation of stack from linedefs and the fixed-global envelope. A reusable byte theorem protects upper caller words at offsets 4 through 64 from collection scratch stores. Complete original aiming execution and its center/right decision now use the derived selector, callback and cursor-call guards instead of assuming them separately. All other complete-query premises remain: initial memory, geometry, live collection and source contracts, catalog guards, capacity, stamp freshness and return protection. Placement and reserve are not proved for reachable states. No runtime or machine-semantic changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: selector, callback and cursor-call guards derived and joined to complete query/decision; strict inherited axiom audit.')
if __name__=='__main__':main()

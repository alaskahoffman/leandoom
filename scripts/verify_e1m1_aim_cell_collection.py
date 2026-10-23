#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_cell_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimCellStamps': ['line_reads', 'global', 'reads'], 'E1M1AimCellWalk': ['buffer_word', 'global_array', 'word', 'global_safe', 'reads_safe', 'scene_safe', 'selection_safe'], 'E1M1AimCellCollection': ['payload', 'images', 'lookup_ready', 'setup_then_collection']}
CONTRACTS=[('E1M1AimCellStamps', 'line_reads', 'stack q c placement i a member'), ('E1M1AimCellStamps', 'global', 'stack q c placement a inside'), ('E1M1AimCellStamps', 'reads', 'stack q c placement'), ('E1M1AimCellWalk', 'buffer_word', 'k hk off member'), ('E1M1AimCellWalk', 'global_array', 'a member'), ('E1M1AimCellWalk', 'word', 'stack r sp lines a reserve inside separate array stamps'), ('E1M1AimCellWalk', 'global_safe', 'stack q c placement reserve a member'), ('E1M1AimCellWalk', 'reads_safe', 'stack q c placement reserve'), ('E1M1AimCellWalk', 'scene_safe', 'stack q c placement reserve'), ('E1M1AimCellWalk', 'selection_safe', 'stack q c placement reserve'), ('E1M1AimCellCollection', 'payload', 'stack q c m n placement reserve before frame'), ('E1M1AimCellCollection', 'images', 'stack q cells m n placement reserve before frame'), ('E1M1AimCellCollection', 'lookup_ready', 'stackRegion s q c placement reserve image contracts stack scanStack items'), ('E1M1AimCellCollection', 'setup_then_collection', 'stack s q c n placement setupReserve walkReserve before frame')]
NAMESPACE='Doom.Verification.ExtractedAimCellCollection'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Layout':'E1M1AimCellStamps',
      'linePointer':'E1M1ScanGeometry','buffer':'E1M1AimCellWalk','globals':'E1M1AimCellWalk'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimCellCollection\n'+previous.certificate(data,raw)
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
    out=ROOT/'artifacts/e1m1-aim-cell-collection';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimCellCollection'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Cell payload read protection during collection is derived from bounded line fields, vertex/actor/blockhead separation from the linedef array, fixed-global separation, and the existing 212-byte reserve below q.sp. All existing scene and selected-head protection fields are reconstructed, including initialized trace and active globals. These guards feed actual original line lookup readiness and transport of payloads and all future cell images through existing collection frames; setup-to-collection payload transport no longer assumes an intermediate payload. Initial/live allocation, memory contents, numeric contracts, actual scan pointers, execution frames, other caller/record guards, capacity, freshness and reachable-state preservation remain obligations. No runtime or machine-semantic changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: cell collection guards derived and joined to original lookup and future-image transport; strict inherited axiom audit.')
if __name__=='__main__':main()

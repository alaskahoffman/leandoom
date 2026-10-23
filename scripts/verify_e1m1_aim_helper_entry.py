#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_global_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimHelperRegions': ['opening_reads', 'read_word', 'record_word', 'records', 'cursor', 'clipping_reads', 'return_safe', 'helper', 'layout', 'callback_records'], 'E1M1AimHelperEntry': ['other', 'initial', 'remaining', 'controller']}
CONTRACTS=[('E1M1AimHelperRegions', 'opening_reads', 'stack q s a placement reserve position inside fixed'), ('E1M1AimHelperRegions', 'read_word', 'stack q s a placement reserve position inside fixed'), ('E1M1AimHelperRegions', 'record_word', 'stack q s a placement reserve position inside'), ('E1M1AimHelperRegions', 'records', 'stack q s hits placement reserve position capacity'), ('E1M1AimHelperRegions', 'cursor', 'stack q s placement reserve position'), ('E1M1AimHelperRegions', 'clipping_reads', 'stack q s placement reserve position'), ('E1M1AimHelperRegions', 'return_safe', 'stack q s placement reserve position'), ('E1M1AimHelperRegions', 'helper', 'stack q s placement reserve position'), ('E1M1AimHelperRegions', 'layout', 'stack q s hits placement reserve position capacity'), ('E1M1AimHelperRegions', 'callback_records', 'stack q s hit line front back ff fc bf bc hits lookup placement reserve position capacity input image'), ('E1M1AimHelperEntry', 'other', 'q stack s scene shooter hits portals walls who placement reserve capacity input'), ('E1M1AimHelperEntry', 'initial', 'q stack s scene shooter hits portals walls who reserve placement walkReserve globalPlacement capacity position other'), ('E1M1AimHelperEntry', 'remaining', 'q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement walkReserve globalPlacement capacity position other'), ('E1M1AimHelperEntry', 'controller', 'q stack s f angle scene shooter hits portals walls who room top bound placement walkReserve globalPlacement capacity position other value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimHelperEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Layout':'E1M1AimGlobalRegions',
      'OtherInputs':'E1M1AimHelperEntry','Portal':'E1M1AimCatalog','resolve':'E1M1ThingFinish','values':'E1M1AimGlobalRegions','stable':'E1M1AimGlobalRegions','recordArea':'E1M1AimHelperRegions'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimHelperEntry\n'+previous.certificate(data,raw)
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
    out=ROOT/'artifacts/e1m1-aim-helper-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimHelperEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Derive the complete eleven-field fixed callback layout from existing global/stack/line placement, 212-byte reserve, actual callback ESP and explicit hits.size<=128. Protect record/cursor reads during callbacks, saved return words and opening/clipping operands. Apply derived record guards to the actual open-line callback result, retaining its original inputs and pre-callback memory image. Remove layout from residual catalog inputs in initial, traversal and controller joins; retain four memory-content/identity catalog fields and all other contracts. Parent marking and collection writes remain outside this callback preservation frame. Reachable capacity, allocation, encoding, numeric/source contracts and freshness remain obligations. No runtime or machine-semantic changes; inherited emulator evidence, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete fixed callback layout derived and joined to catalog and actual record preservation; strict inherited axiom audit.')
if __name__=='__main__':main()

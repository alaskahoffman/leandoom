#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_allocated_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimSetupFootprint': ['stack_word', 'controller_reserve', 'safe', 'region_safe'], 'E1M1AimMapRegions': ['fixed_globals', 'stores_contained', 'global_safe', 'word_safe', 'covered'], 'E1M1AimMapEntry': ['inputs', 'execution', 'controller_map']}
CONTRACTS=[('E1M1AimSetupFootprint', 'stack_word', 'stack s reserve n low high'), ('E1M1AimSetupFootprint', 'controller_reserve', 'stack s angle room top bound'), ('E1M1AimSetupFootprint', 'safe', 's a apart'), ('E1M1AimSetupFootprint', 'region_safe', 'stack region s a reserve inside separate fixed'), ('E1M1AimMapRegions', 'fixed_globals', ''), ('E1M1AimMapRegions', 'stores_contained', ''), ('E1M1AimMapRegions', 'global_safe', 'stack s base a reserve placement member'), ('E1M1AimMapRegions', 'word_safe', 'stack s base reserve placement i hi'), ('E1M1AimMapRegions', 'covered', 'stack base words placement size'), ('E1M1AimMapEntry', 'inputs', 'stack s base lines words reserve placement size values'), ('E1M1AimMapEntry', 'execution', 'stack s f base lines words reserve placement size values'), ('E1M1AimMapEntry', 'controller_map', 'stack s f base lines words placement room top bound size values')]
NAMESPACE='Doom.Verification.ExtractedAimMapEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Reserve':'E1M1AimSetupFootprint',
      'writes':'E1M1AimSetupFootprint','globals':'E1M1AimSetupFootprint',
      'globalStores':'E1M1AimMapRegions','mapGlobals':'E1M1AimMapRegions',
      'Layout':'E1M1AimMapRegions','Values':'E1M1AimMapEntry'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimMapEntry\n'+previous.certificate(data,raw)
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
    out=ROOT/'artifacts/e1m1-aim-map-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimMapEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='All existing blockmap MapInputs protection predicates are derived from scalar stack reserve and region placement, with only memory values/image still supplied. The query setup footprint contains fixed globals and a 104-byte conservative stack window below query entry, or 124 bytes including the outer prologue. This covers the established ray/aim/path setup protection contract, including axis/intercept helper and iterator-entry slots; it is not a full aiming stack bound. Fixed map globals are proved byte-disjoint from every fixed setup store; the 6924-byte map read-window envelope is protected from those stores and stack writes. The reconstructed input contract feeds the original 36-instruction query execution and map preservation through the actual P_PathTraverse CALL, and can be obtained from memory before the outer controller prologue. The pinned WAD array instantiates the constructor. Startup encodings and allocation/stack placement, dynamic callbacks and whole-query preservation, arithmetic, capacity and reachable freshness remain open. Existing complete controller theorem unchanged and conditional. No runtime or instruction-semantic changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: query-setup map protection derived and connected to real query entry; strict inherited axiom audit.')
if __name__=='__main__':main()

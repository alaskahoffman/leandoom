#!/usr/bin/env python3
"""Certify portal preservation through the authenticated original linedef loop."""
import argparse,json,re,subprocess
import verify_e1m1_aim_loaded_portal as previous
import verify_original_line_scan as scan
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimLoadedScanRegions': ['cursor_nat', 'record_field', 'records_apart', 'protected_read', 'earlier_field', 'sector_field', 'portal_reads', 'sector_safe'], 'E1M1AimLoadedScan': ['iteration_suffix', 'retained', 'established', 'execution']}
CONTRACTS=[('E1M1AimLoadedScanRegions', 'cursor_nat', 'base n bound'), ('E1M1AimLoadedScanRegions', 'record_field', 'total base i off bound inside fits'), ('E1M1AimLoadedScanRegions', 'records_apart', 'total base i j bound order inside'), ('E1M1AimLoadedScanRegions', 'protected_read', 'r stack a output sp read bound lineApart stackApart reserve'), ('E1M1AimLoadedScanRegions', 'earlier_field', 'total base sp stack i j off layout reserve order inside fits'), ('E1M1AimLoadedScanRegions', 'sector_field', 'total base address sp stack j off layout sector reserve inside fits'), ('E1M1AimLoadedScanRegions', 'portal_reads', 'total base sp stack i j p layout front back reserve order inside'), ('E1M1AimLoadedScanRegions', 'sector_safe', 'total base sp stack i p layout front back reserve inside'), ('E1M1AimLoadedScan', 'iteration_suffix', 's'), ('E1M1AimLoadedScan', 'retained', 'total raw base sp stack s f i hit p loop ready layout front back reserve inside initial'), ('E1M1AimLoadedScan', 'established', 'total raw base sp stack s f i hit p loop ready layout front back reserve inside source present heights kind two'), ('E1M1AimLoadedScan', 'execution', 'total raw base sp stack s f i hit p loop ready arithmetic layout front back reserve inside source present heights kind two')]
NAMESPACE='Doom.Verification.ExtractedAimLoadedScan'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region': 'E1M1NoiseAllocation', 'Portal': 'E1M1AimCatalog', 'region': 'E1M1AimObjectRegions', 'cursor': 'E1M1LineScan', 'states': 'E1M1LineScan', 'Layout': 'E1M1AimLoadedScanRegions', 'Sector': 'E1M1AimLoadedScanRegions', 'Reserve': 'E1M1AimLoadedScanRegions'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def scan_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    extraction=scan.iteration.extraction
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw,units={},{}
    for name in ['original-div-memory','original-line-setup','original-line-geometry','original-line-load','original-line-cache']:
        spec=json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())
        raw.update(extraction.extract(binary,profile,spec))
        units.update({'scan_'+k:v for k,v in spec['units'].items()})
    data,wp=scan.iteration.setup.geometry.geometry_data()
    require(wp['exe_sha256']==profile['exe_sha256'],'scan executable mismatch')
    return raw,units,data,wp

def combined_units(aim_units,scan_units):
    _,loader_units,_=previous.loader_data()
    units={**aim_units,**loader_units}
    by_offset={u['code_offset']:u for u in units.values()}
    for name,unit in scan_units.items():
        old=by_offset.get(unit['code_offset'])
        if old is not None:
            require(old==unit,'inconsistent overlapping byte range')
        else:
            units[name]=unit;by_offset[unit['code_offset']]=unit
    return units

def certificate(data,raw,scan_inputs=None):
    source='import Doom.Proofs.E1M1AimLoadedScan\n'+previous.certificate(data,raw)
    if scan_inputs is None:scan_inputs=scan_data()
    source+='\n'+scan.certificate(scan_inputs[0],scan_inputs[2]).split('\n',1)[1]
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
    before,rest=output.split(marker,1)
    loader_marker="'Doom.Verification.ExtractedLineIteration.division_checked'"
    inherited,loaded=before.split(loader_marker,1)
    previous.audit(inherited);scan.audit(loader_marker+loaded);rest=(marker+rest).strip()
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
    scan_inputs=scan_data();require(scan_inputs[3]['exe_sha256']==profile['exe_sha256'],'scan executable mismatch')
    require(scan_inputs[3]['wad_sha256']==mp['wad_sha256'],'scan WAD mismatch')
    units=combined_units(spec['units'],scan_inputs[1])
    out=ROOT/'artifacts/e1m1-aim-loaded-scan';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan_inputs))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimLoadedScan'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=units,cells=len(data['cells']),
      scope='Portal values established at the actual reached copy/cache suffix survive all later linedef iterations. Disjoint bounded line-array, sector-prefix and stack regions derive all later write guards. The same result is paired with the uninterrupted original positive-count loader loop. Raw inputs, sector values and flags at the reached suffix, initial loop representation and arithmetic remain premises; actual allocation, remaining startup and reachable-state preservation are not established. Six existing loop ranges are newly joined; no new decoder, instruction semantics or emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: loaded portal survives complete original linedef scan; inherited and full-loop certificates strictly audited.')
if __name__=='__main__':main()

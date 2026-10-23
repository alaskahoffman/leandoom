#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_object_entry as previous
import verify_original_line_load as loader
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimLoadedPortal': ['pointers', 'back_index', 'flags', 'sectors', 'image', 'values', 'wall', 'transport', 'catalog', 'execution']}
CONTRACTS=[('E1M1AimLoadedPortal', 'pointers', 'e s source'), ('E1M1AimLoadedPortal', 'back_index', 'e s source'), ('E1M1AimLoadedPortal', 'flags', 's'), ('E1M1AimLoadedPortal', 'sectors', 'address p s position safe values'), ('E1M1AimLoadedPortal', 'image', 'address p s source present safe values'), ('E1M1AimLoadedPortal', 'values', 'address p s hit source present safe heights kind two'), ('E1M1AimLoadedPortal', 'wall', 's hit kind solid'), ('E1M1AimLoadedPortal', 'transport', 'before after hit address p initial frame'), ('E1M1AimLoadedPortal', 'catalog', 'address p s aim hit source present safe heights kind two frame stack sp reserve position lineStorage frontStorage backStorage'), ('E1M1AimLoadedPortal', 'execution', 'address p s f hit source present safe heights kind two')]
NAMESPACE='Doom.Verification.ExtractedAimLoadedPortal'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region': 'E1M1NoiseAllocation', 'Portal': 'E1M1AimCatalog', 'line': 'E1M1AimLoadedPortal', 'SectorValues': 'E1M1AimLoadedPortal', 'SectorSafe': 'E1M1AimLoadedPortal', 'reads': 'E1M1AimLoadedPortal'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def loader_data():
    profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary=loader.extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw,units={},{}
    for name in ['original-line-load','original-line-cache']:
        spec=json.loads((ROOT/'tests/reference'/f'{name}.json').read_text())
        raw.update(loader.extraction.extract(binary,profile,spec))
        units.update({'loader_'+k:v for k,v in spec['units'].items()})
    return raw,units,profile['exe_sha256']

def certificate(data,raw,loader_raw=None):
    source='import Doom.Proofs.E1M1AimLoadedPortal\n'+previous.certificate(data,raw)
    if loader_raw is None:loader_raw=loader_data()[0]
    source+='\n'+loader.certificate(loader_raw).split('\n',1)[1]
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
    loader_marker="'Doom.Verification.ExtractedLineLoad.copy_checked'"
    inherited,loaded=before.split(loader_marker,1)
    previous.audit(inherited);loader.audit(loader_marker+loaded);rest=(marker+rest).strip()
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
    loader_raw,loader_units,loader_hash=loader_data();require(loader_hash==profile['exe_sha256'],'loader executable mismatch')
    out=ROOT/'artifacts/e1m1-aim-loaded-portal';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,loader_raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimLoadedPortal'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units={**spec['units'],**loader_units},cells=len(data['cells']),
      scope='Derive aiming portal pointers and copied back-side index from the actual existing original line-loader suffix, preserve flags and sector heights, and connect the result through an explicit eight-word later read frame to a guarded aiming catalog. Sector values, raw side-table inputs, back-side presence, loader separation and later storage/frame remain premises. No whole loader startup, sector-update preservation, actor initialization or reachable aiming theorem. Adds three existing authenticated loader ranges to the inherited 51-range aiming certificate; no new decoder or instruction semantics and no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actual loader output establishes aiming portal values; inherited and loader byte certificates strictly audited.')
if __name__=='__main__':main()

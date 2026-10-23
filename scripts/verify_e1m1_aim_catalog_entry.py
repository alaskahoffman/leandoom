#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_map_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimObjectRegions': ['field', 'actor', 'wall', 'opening', 'setup_safe', 'opening_safe'], 'E1M1AimCatalogRegions': ['located', 'prologue_safe', 'read'], 'E1M1AimCatalogEntry': ['initial', 'remaining', 'controller', 'opening_heights']}
CONTRACTS=[('E1M1AimObjectRegions', 'field', 'stack base bytes off storage fits'), ('E1M1AimObjectRegions', 'actor', 'stack base storage'), ('E1M1AimObjectRegions', 'wall', 'stack line storage'), ('E1M1AimObjectRegions', 'opening', 'stack line front back lineStorage frontStorage backStorage'), ('E1M1AimObjectRegions', 'setup_safe', 'stack s a reserve located'), ('E1M1AimObjectRegions', 'opening_safe', 'stack s front back reserve lineStorage frontStorage backStorage'), ('E1M1AimCatalogRegions', 'located', 'stack hits lookup portals placement'), ('E1M1AimCatalogRegions', 'prologue_safe', 'stack s hits lookup portals reserve placement'), ('E1M1AimCatalogRegions', 'read', 'q stack s hits portals reserve placement later'), ('E1M1AimCatalogEntry', 'initial', 'q stack s scene shooter hits portals walls who reserve placement later other'), ('E1M1AimCatalogEntry', 'remaining', 'q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement later other'), ('E1M1AimCatalogEntry', 'controller', 'q stack s f angle scene shooter hits portals walls who room top bound placement later other value angleSafe'), ('E1M1AimCatalogEntry', 'opening_heights', 'stack s front back ff fc bf bc reserve lineStorage frontStorage backStorage side frontPtr backPtr frontFloor frontCeiling backFloor backCeiling')]
NAMESPACE='Doom.Verification.ExtractedAimCatalogEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Storage':'E1M1AimObjectRegions',
      'Located':'E1M1AimObjectRegions','OpeningReserve':'E1M1AimObjectRegions',
      'Layout':'E1M1AimCatalogRegions','OtherInputs':'E1M1AimCatalogEntry',
      'Portal':'E1M1AimCatalog','resolve':'E1M1ThingFinish'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimCatalogEntry\n'+previous.certificate(data,raw)
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
    out=ROOT/'artifacts/e1m1-aim-catalog-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimCatalogEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Actor, wall and portal read locations are derived from 108-byte actor, 62-byte linedef and 8-byte sector-prefix protection regions, with unaligned fields and shared read-only sectors supported. Region placement derives query-setup and outer-prologue protection for the complete catalog read set. Existing later collection/selection and ordered-callback guards remain explicit. The old pre-ray Initial catalog is reconstructed with its three read families supplied by the new proof, transported through actual query setup, and also constructed after the original outer prologue from original-memory contracts. A separate sixteen-byte opening-helper reserve plus the same storage regions discharges its stack/global protection and feeds the existing signed floor/ceiling extrema theorem. These are conditional region guarantees, not DOS allocation or reachable-state theorems. Object identities, memory encodings, later frames, arithmetic/capacity/freshness and wider memory preservation remain obligations. No runtime or instruction-semantic changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: actor/opening region guards connected to catalog construction and opening helper; strict inherited axiom audit.')
if __name__=='__main__':main()

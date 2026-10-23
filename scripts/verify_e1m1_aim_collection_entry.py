#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_catalog_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimWalkRegions': ['stack_apart', 'global_apart', 'array_safe', 'collection', 'selection', 'ordered'], 'E1M1AimStampRegions': ['line_field', 'external_field', 'stamps'], 'E1M1AimCollectionEntry': ['later', 'stable', 'word', 'initial', 'remaining', 'controller']}
CONTRACTS=[('E1M1AimWalkRegions', 'stack_apart', 'stack sp a offset reserve located fits'), ('E1M1AimWalkRegions', 'global_apart', 'stack a b located inside'), ('E1M1AimWalkRegions', 'array_safe', 'stack a located'), ('E1M1AimWalkRegions', 'collection', 'stack sp lines a reserve located stamps'), ('E1M1AimWalkRegions', 'selection', 'stack sp a reserve located'), ('E1M1AimWalkRegions', 'ordered', 'stack sp a s reserve located position'), ('E1M1AimStampRegions', 'line_field', 'lines i j off hi hj fits'), ('E1M1AimStampRegions', 'external_field', 'lines base bytes off j lineBound bound separate fits hj'), ('E1M1AimStampRegions', 'stamps', 'stack lines hits lookup portals placement'), ('E1M1AimCollectionEntry', 'later', 'q stack hits portals walkReserve placement'), ('E1M1AimCollectionEntry', 'stable', 'q stack s hits portals walkReserve placement'), ('E1M1AimCollectionEntry', 'word', 'q stack s out hits portals marked a walkReserve placement member frame pointer bounded'), ('E1M1AimCollectionEntry', 'initial', 'q stack s scene shooter hits portals walls who reserve placement walkReserve other'), ('E1M1AimCollectionEntry', 'remaining', 'q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement walkReserve other'), ('E1M1AimCollectionEntry', 'controller', 'q stack s f angle scene shooter hits portals walls who room top bound placement walkReserve other value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimCollectionEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Reserve':'E1M1AimWalkRegions',
      'Located':'E1M1AimObjectRegions','Layout':'E1M1AimStampRegions',
      'OtherInputs':'E1M1AimCatalogEntry','Portal':'E1M1AimCatalog','resolve':'E1M1ThingFinish'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimCollectionEntry\n'+previous.certificate(data,raw)
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
    out=ROOT/'artifacts/e1m1-aim-collection-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimCollectionEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Collection, first-selection and persistent ordered-hit word guards are derived from the existing object regions and a conservative 212-byte reserve below the context anchor q.sp. The fixed global envelope encloses all 128 intercept records and callback globals. A separate universal byte proof separates bounded linedef reads ending before offset 54 from all 475 visit stamps, even at a wrapping line-array base. Actor and sector prefixes use explicit separation from the line array. These representation facts derive every catalog-read stamp guard and remove the later collection/first-selection read premise from the initial, traversal and outer-controller catalog constructors. The ordered guard feeds the existing callback/mark/scan word frame; its execution and bounded-index premises remain. This does not prove live allocation, object identity/content, buffer capacity, stamp freshness, all callback/record/caller invariants or reachable-state preservation. The 212-byte reserve is relative to q.sp and covers the named guards, not a universal stack bound. No runtime or instruction-semantic changes; emulator evidence inherited, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: collection, stamp and ordered-read guards derived and connected to catalog joins; strict inherited axiom audit.')
if __name__=='__main__':main()

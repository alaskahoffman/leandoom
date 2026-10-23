#!/usr/bin/env python3
"""Certify range-based aiming entry guards against the inherited DOS/map certificate."""
import argparse,json,re,subprocess
import verify_e1m1_aim_caller_entry as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER+'\nopen Doom.Proofs.E1M1NoiseAllocation (Region)\n'
GROUPS={'E1M1AimGlobalRegions': ['contained', 'array', 'push', 'collection', 'path_setup', 'selection', 'later', 'ordered', 'clip', 'floor_word'], 'E1M1AimGlobalEntry': ['other', 'initial', 'remaining', 'controller']}
CONTRACTS=[('E1M1AimGlobalRegions', 'contained', 'a member'), ('E1M1AimGlobalRegions', 'array', 'a member'), ('E1M1AimGlobalRegions', 'push', 'stack sp lines a off placement reserve inside fits'), ('E1M1AimGlobalRegions', 'collection', 'stack q a placement reserve member'), ('E1M1AimGlobalRegions', 'path_setup', 'stack q s a placement reserve position member'), ('E1M1AimGlobalRegions', 'selection', 'stack q a placement reserve member'), ('E1M1AimGlobalRegions', 'later', 'stack q s a placement reserve position member'), ('E1M1AimGlobalRegions', 'ordered', 'stack q s a placement reserve position member'), ('E1M1AimGlobalRegions', 'clip', 'stack q s placement reserve position'), ('E1M1AimGlobalRegions', 'floor_word', 'stack q s a placement reserve position member'), ('E1M1AimGlobalEntry', 'other', 'q stack s scene shooter hits portals walls who placement reserve position input'), ('E1M1AimGlobalEntry', 'initial', 'q stack s scene shooter hits portals walls who reserve placement walkReserve globalPlacement position other'), ('E1M1AimGlobalEntry', 'remaining', 'q stack s scene shooter thing angle distance hits portals walls who geometry reserve placement walkReserve globalPlacement position other'), ('E1M1AimGlobalEntry', 'controller', 'q stack s f angle scene shooter hits portals walls who room top bound placement walkReserve globalPlacement position other value angleSafe')]
NAMESPACE='Doom.Verification.ExtractedAimGlobalEntry'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','Layout':'E1M1AimGlobalRegions',
      'OtherInputs':'E1M1AimGlobalEntry','Portal':'E1M1AimCatalog','resolve':'E1M1ThingFinish','values':'E1M1AimGlobalRegions','stable':'E1M1AimGlobalRegions'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimGlobalEntry\n'+previous.certificate(data,raw)
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
    out=ROOT/'artifacts/e1m1-aim-global-entry';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimGlobalEntry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Derive seven fixed-global guard fields and join them to initial, traversal and controller catalogs. Six setup values survive collection; only four are StableWord through continuing callbacks, with clipping bounds deliberately mutable and target-selection writes outside that frame. Applies derived clip guards to the actual floor helper result. Requires line/global separation in addition to prior line/stack/global placement and 212-byte reserve. Five residual catalog fields retain nested helper/record layout and map/object value/identity obligations. Actual reachable allocation, encoding, numeric/source contracts, capacity and freshness remain unproved. No runtime or machine-semantic changes; inherited emulator evidence, not rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: phase-specific fixed-global guards derived and joined to catalog inputs and floor helper; strict inherited axiom audit.')
if __name__=='__main__':main()

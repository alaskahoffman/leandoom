#!/usr/bin/env python3
"""Join raw flags to the initial-image portal execution theorem."""
import argparse,json,re,subprocess
import verify_e1m1_aim_initial_portal as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimLoaderFlags': ['prepared_frame', 'before_frame', 'copy_frame', 'flag_byte'], 'E1M1AimRawPortal': ['flag_stack', 'flag_at_copy', 'established', 'execution_from_image']}
CONTRACTS=[('E1M1AimLoaderFlags', 'prepared_frame', 's a safe'), ('E1M1AimLoaderFlags', 'before_frame', 's a safe'), ('E1M1AimLoaderFlags', 'copy_frame', 's a safe'), ('E1M1AimLoaderFlags', 'flag_byte', 's stack'), ('E1M1AimRawPortal', 'flag_stack', 'total base sp stack i layout reserve'), ('E1M1AimRawPortal', 'flag_at_copy', 'total raw base sp stack s f i loop ready layout reserve flagSourceSafe'), ('E1M1AimRawPortal', 'established', 'total records raw sideBase base sp stack s f i hit ff fc bf bc loop ready separate image layout front back reserve present heights kind flagSourceSafe two'), ('E1M1AimRawPortal', 'execution_from_image', 'total records geometry raw sideBase vertexBase base sp stack s f i hit ff fc bf bc loop ready verticesSafe vertices good separate image layout front back reserve present heights kind flagSourceSafe two')]
REUSED=['Doom.Proofs.OriginalLineSetup.metadata_fields','Doom.Proofs.OriginalLineGeometry.bounds_frame','Doom.Proofs.OriginalDivMemory.result_frame']
NAMESPACE='Doom.Verification.ExtractedAimRawPortal'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','cursor':'E1M1LineScan','states':'E1M1LineScan','portal':'E1M1AimInitialPortal','Safe':'E1M1AimLoaderFlags'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def names():
    return ([NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+
      ['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED)

def certificate(data,raw,scan_inputs=None):
    source='import Doom.Proofs.E1M1AimRawPortal\n'+previous.certificate(data,raw,scan_inputs)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        source+='namespace '+module+'\n'+decl+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='end '+NAMESPACE+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker="'"+names()[0]+"'"
    require(marker in output,'missing initial portal audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    for full in names():
        match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing audit: '+full)
        require({a.strip() for a in (match[1] or '').split(',') if a.strip()}<={'propext','Quot.sound','Classical.choice'},'unexpected axioms')
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    data,mp=pinned_data();spec,profile,raw=extracted();scan_inputs=previous.previous.scan_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan_inputs[3]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan_inputs[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-raw-portal';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan_inputs))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimRawPortal'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],
      units=previous.previous.combined_units(spec['units'],scan_inputs[1]),cells=len(data['cells']),
      reused_declarations=REUSED,
      scope='Exact raw flag byte copied by metadata and preserved through axis/diagonal geometry and stack writes. Initial raw flags replace the last reached-prefix portal content premise. Static protection of raw flag reads during earlier iterations, initial side/vertex/sector representations, allocation/separation and finite geometry safety remain required. No complete startup or reachable aiming theorem; no new binary ranges, runtime, decoder or instruction semantics.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: raw flags joined to initial-image portal scan, with no reached-content premises; strict inherited audit.')
if __name__=='__main__':main()

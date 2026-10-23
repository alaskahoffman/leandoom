#!/usr/bin/env python3
"""Join initial side/sector data and existing geometry safety to the portal scan."""
import argparse,json,re,subprocess
import verify_e1m1_aim_loaded_scan as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimInitialPortal':['source_at_copy','sector_word_at_copy','sectors_at_copy','established','execution_from_image']}
CONTRACTS=[
 ('E1M1AimInitialPortal','source_at_copy','total records raw sideBase base sp s f i loop ready separate image'),
 ('E1M1AimInitialPortal','sector_word_at_copy','total raw base sp address stack s f i off loop ready layout sector reserve fits'),
 ('E1M1AimInitialPortal','sectors_at_copy','total raw base sp stack s f i p loop ready layout front back reserve initial'),
 ('E1M1AimInitialPortal','established','total records raw sideBase base sp stack s f i hit ff fc bf bc loop ready separate image layout front back reserve present heights kind two'),
 ('E1M1AimInitialPortal','execution_from_image','total records geometry raw sideBase vertexBase base sp stack s f i hit ff fc bf bc loop ready verticesSafe vertices good separate image layout front back reserve present heights kind two')]
REUSED=['Doom.Proofs.E1M1LineOutput.'+n for n in ['copy_source','copy_frame','image_preserved']]
REUSED+=['Doom.Proofs.E1M1LineSource.'+n for n in ['safe_of_source','arithmetic_of_image','scan_from_image']]
NAMESPACE='Doom.Verification.ExtractedAimInitialPortal'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Region':'E1M1NoiseAllocation','cursor':'E1M1LineScan','states':'E1M1LineScan','portal':'E1M1AimInitialPortal'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def names():
    return ([NAMESPACE+'.'+m+'.'+n+'_checked' for m,n,_ in CONTRACTS]+
      ['Doom.Proofs.'+m+'.'+n for m,group in GROUPS.items() for n in group]+REUSED)

def certificate(data,raw,scan_inputs=None):
    source='import Doom.Proofs.E1M1AimInitialPortal\n'+previous.certificate(data,raw,scan_inputs)
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
    data,mp=pinned_data();spec,profile,raw=extracted();scan_inputs=previous.scan_data()
    require(mp['exe_sha256']==profile['exe_sha256']==scan_inputs[3]['exe_sha256'],'executable mismatch')
    require(mp['wad_sha256']==scan_inputs[3]['wad_sha256'],'WAD mismatch')
    out=ROOT/'artifacts/e1m1-aim-initial-portal';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw,scan_inputs))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimInitialPortal'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],
      units=previous.combined_units(spec['units'],scan_inputs[1]),cells=len(data['cells']),
      reused_declarations=REUSED,
      scope='Initial side image and sector heights establish portal values at full line-scan completion. Reuses existing source-image preservation, copy-source construction and geometry-image arithmetic safety. Reached raw-side/sector images and per-reached-state arithmetic are derived, not assumed. Initial images, finite good geometry, storage separation, initial loop representation and the reached two-sided flag remain premises. No complete startup or reachable aiming theorem; no new byte ranges, decoder, runtime or instruction semantics.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: initial side/sector images and existing arithmetic proof joined to complete portal scan; strict inherited audit.')
if __name__=='__main__':main()

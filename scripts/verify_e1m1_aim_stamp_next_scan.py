#!/usr/bin/env python3
"""Certify exact line-stamp history and conditional next-epoch freshness."""
import argparse,json,re,subprocess
import verify_e1m1_aim_retry_inputs as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimStampImage':['start','transport','fresh','successor_ne','next_fresh','bounded_fresh','restart'],
 'E1M1AimStampScan':['step_image','scan_image','run_image','finished_image'],
 'E1M1AimStampNextScan':['execution','from_entry']}
SCAN_ARGS='initial n base resolve h lines count layout i s r inv'
NEXT_ARGS='s sp cursor lines objects trace c data stack list items ids ready layout stamps f r tracked epoch seen size represented'
CONTRACTS=[
 ('E1M1AimStampImage','start','m lines epoch seen represented'),
 ('E1M1AimStampImage','transport','origin m n lines epoch seen image counter stamps'),
 ('E1M1AimStampImage','fresh','origin current lines epoch future seen image different before'),
 ('E1M1AimStampImage','successor_ne','epoch'),
 ('E1M1AimStampImage','next_fresh','origin current lines epoch seen image before'),
 ('E1M1AimStampImage','bounded_fresh','m lines epoch count bounded noWrap'),
 ('E1M1AimStampImage','restart','origin s lines epoch seen ox oy sx sy ex ey geometry image before epochSafe stampSafe'),
 ('E1M1AimStampScan','step_image',SCAN_ARGS+' hi origin epoch seen size represented image'),
 ('E1M1AimStampScan','scan_image',SCAN_ARGS+' k bound origin epoch seen size represented image'),
 ('E1M1AimStampScan','run_image',SCAN_ARGS+' k bound keep origin epoch seen size represented image'),
 ('E1M1AimStampScan','finished_image','initial n base resolve h lines count layout f r tracked keep origin epoch seen size represented image'),
 ('E1M1AimStampNextScan','execution',NEXT_ARGS+' origin image'),
 ('E1M1AimStampNextScan','from_entry',NEXT_ARGS)]
NAMESPACE='Doom.Verification.ExtractedAimStampNextScan'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Image':'E1M1AimStampImage','Fresh':'E1M1AimStampImage',
      'Represents':'OriginalLineVisits','stamp':'OriginalLineVisits','markPrefix':'OriginalLineVisits',
      'Initial':'OriginalLineMixedInvariant','Stable':'OriginalLineMixedInvariant',
      'step':'OriginalLineMixedInvariant','run':'OriginalLineMixedInvariant','finished':'OriginalLineMixedInvariant',
      'LineData':'E1M1ScanContracts','candidates':'E1M1ScanContracts','Ready':'E1M1NextCallbackReady',
      'result':'E1M1NextLineScan'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimStampNextScan\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimRetryInputs.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimRetryInputs.linked_checked',
      'def returnProgram := Doom.Verification.ExtractedAimCompletedReturn.linked',
      'theorem returnProgram_checked : returnProgram=E1M1AimCompletedReturn.program :=',
      '  Doom.Verification.ExtractedAimCompletedReturn.linked_checked',
      ''])
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1AimProgramLink.program','linked').replace('E1M1AimCompletedReturn.program','returnProgram')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'linked' in decl:source+='rw [linked_checked]\n  '
        if 'returnProgram' in decl:source+='rw [returnProgram_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n#print axioms returnProgram_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".linked_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.linked_checked',NAMESPACE+'.returnProgram_checked']
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
    out=ROOT/'artifacts/e1m1-aim-stamp-next-scan';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimStampNextScan'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='An exact stamp image retains original values of unvisited lines and current-epoch values of visited lines. It is preserved by individual callbacks, early-stopping scans, continuing scans and sentinel return. The actual next-cell line-scan execution under the authenticated combined program carries this image and derives next-epoch freshness from explicit origin-word freshness. A bounded non-wrapping stamp condition is sufficient; modular successor inequality alone is not. A separate restart theorem uses the image to supply the existing actual path-initialization visited-array contract. The image is not yet threaded through the full cell/object/grid loop, ordered aiming and retry; complete next traversal entry, reachable freshness and full three-probe correspondence remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exact stamp history follows line scans and yields conditional next-epoch freshness; strict axiom audit.')
if __name__=='__main__':main()

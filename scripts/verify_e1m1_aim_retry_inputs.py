#!/usr/bin/env python3
"""Certify next-probe data reconstruction and continuous retry ray/setup."""
import argparse,json,re,subprocess
import verify_e1m1_aim_call_frame as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={'E1M1AimRetryData':['safe','map','payload','payload_safe'],
 'E1M1AimRetryGeometry':['angle_bits','samples','geometry'],
 'E1M1AimRetryInputs':['prepared','setup','retry']}
ENTRY_ARGS=previous.previous.ENTRY_ARGS
CONTRACTS=[
 ('E1M1AimRetryData','safe','s t a stack h'),
 ('E1M1AimRetryData','map','s t base lines words w h stack before kept'),
 ('E1M1AimRetryData','payload','m n q c before kept'),
 ('E1M1AimRetryData','payload_safe','s t q c stack h'),
 ('E1M1AimRetryGeometry','angle_bits','second angle'),
 ('E1M1AimRetryGeometry','samples','s t angle distance tables angleReg rangeReg stack kept safe'),
 ('E1M1AimRetryGeometry','geometry','s t thing oldAngle angle oldDistance distance ox oy before tables actor stack angleReg rangeReg kept sampleSafe'),
 ('E1M1AimRetryInputs','prepared','q s next thing angle distance second cells h request controller tables data kept safe'),
 ('E1M1AimRetryInputs','setup','q next thing angle cells pc data'),
 ('E1M1AimRetryInputs','retry',ENTRY_ARGS+' savedSafe returnSafe second nextCells tables nextData watchedRead watchedSafe retrySafe controller resume')]
NAMESPACE='Doom.Verification.ExtractedAimRetryInputs'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'traversal':'E1M1PathMapQuery','resolve':'E1M1ThingFinish',
      'mapReads':'E1M1AimRetryData','cellReads':'E1M1AimRetryData',
      'sampleReads':'E1M1AimRetryGeometry','nextAngle':'E1M1AimRetryGeometry',
      'Prepared':'E1M1AimRetryInputs'}
    if module=='E1M1AimRetryGeometry':owners['reads']=module
    if module=='E1M1AimRetryInputs':owners['reads']=module
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimRetryInputs\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimCallFrame.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimCallFrame.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-retry-inputs';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimRetryInputs'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Derive next-angle geometry, complete blockmap including 16-bit word image, and supplied cell payloads with guards from initial data, full-table encoding, restored retry registers and the whole-call finite memory frame. On a source miss the same authenticated execution now continues through the next ray/setup 36 instructions to path traversal entry, with geometry and map inputs proved there. Protection and initial data for the next read set remain explicit. Cells are supplied, not yet proved to be the next route. No next-epoch/stamp freshness, next collection, hit catalogs, reachable E1M1 invariants or complete three-probe controller is claimed. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: next-probe data derived and next ray/setup joined; strict axiom audit.')
if __name__=='__main__':main()

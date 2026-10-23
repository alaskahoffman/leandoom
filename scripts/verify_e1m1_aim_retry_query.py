#!/usr/bin/env python3
"""Certify original caller-register restoration and continuous aim-to-retry execution."""
import argparse,json,re,subprocess
import verify_e1m1_aim_pre_ray_query as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimCallerRegisters':['saved','setup_saved','restores'],
 'E1M1AimRetryRequest':['execution','memory','request','frame'],
 'E1M1AimRetryQuery':['execution','retry']}
ENTRY_ARGS=previous.ENTRY_ARGS
CONTRACTS=[
 ('E1M1AimCallerRegisters','saved','s'),
 ('E1M1AimCallerRegisters','setup_saved','s safe'),
 ('E1M1AimCallerRegisters','restores','q s out stack safe returnSafe returned'),
 ('E1M1AimRetryRequest','execution','second out answer related miss resume'),
 ('E1M1AimRetryRequest','memory','second out'),
 ('E1M1AimRetryRequest','request','second s out restored'),
 ('E1M1AimRetryRequest','frame','second out a slopeSafe returnSafe'),
 ('E1M1AimRetryQuery','execution',ENTRY_ARGS+' savedSafe returnSafe'),
 ('E1M1AimRetryQuery','retry',ENTRY_ARGS+' savedSafe returnSafe second controller resume')]
NAMESPACE='Doom.Verification.ExtractedAimRetryQuery'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'SavedSafe':'E1M1AimCallerRegisters','Restores':'E1M1AimCallerRegisters',
      'Request':'E1M1AimRetryRequest','Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'traversal':'E1M1PathMapQuery','resolve':'E1M1ThingFinish'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimRetryQuery\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimPreRayQuery.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimPreRayQuery.linked_checked',
      ''])
    for module,name,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+name+'_checked',1)
        decl=decl.replace('E1M1AimProgramLink.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'linked' in decl:source+='rw [linked_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='#print axioms linked_checked\n'
    source+='\n'.join('#print axioms '+m+'.'+n+'_checked' for m,n,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".linked_checked'"
    require(marker in output,'missing query selection audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.linked_checked']
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
    out=ROOT/'artifacts/e1m1-aim-retry-query';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimRetryQuery'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Complete aim query restores original EBP/EDI/ESI/ECX, ESP and original return PC from actual pushes and saved-word preservation, under initial setup-write and return-word protection. On a source miss, the same authenticated execution continues through the actual target decision, retry instructions and next P_AimLineAttack CALL. Next actor/range/angle, stack slot, caller registers and pushed return address are derived, with an explicit initial controller actor/angle relation. Exact memory image/frame covers the two caller-side writes only, not the preceding complete query. No preservation of EBX/EDX/flags is asserted. Next-query memory contracts, execution of all probes, reachable E1M1 invariants and whole-game correspondence remain open. No runtime, decoder, instruction-semantic or binary-range changes; no emulator rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: original caller registers and actual retry request joined to the continuous aim execution; strict axiom audit.')
if __name__=='__main__':main()

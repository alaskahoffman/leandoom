#!/usr/bin/env python3
"""Certify pre-ray payload/catalog transport into the continuous aim-query result."""
import argparse,json,re,subprocess
import verify_e1m1_aim_entry_query as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimPreRayMemory':['safe','later','image','callback','payload'],
 'E1M1AimPreRayCatalog':['shooter','remaining'],
 'E1M1AimPreRayQuery':['execution','decision']}
ENTRY_ARGS=previous.ENTRY_ARGS
CONTRACTS=[
 ('E1M1AimPreRayMemory','safe','s a h'),
 ('E1M1AimPreRayMemory','later','q s a h'),
 ('E1M1AimPreRayMemory','image','q s'),
 ('E1M1AimPreRayMemory','callback','q s h'),
 ('E1M1AimPreRayMemory','payload','s q c data h'),
 ('E1M1AimPreRayCatalog','shooter','s thing angle distance ox oy geometry'),
 ('E1M1AimPreRayCatalog','remaining','q s scene shooterId thing angle distance hits portals walls who geometry h'),
 ('E1M1AimPreRayQuery','execution',ENTRY_ARGS),
 ('E1M1AimPreRayQuery','decision',ENTRY_ARGS+' second returnSafe resume')]
NAMESPACE='Doom.Verification.ExtractedAimPreRayQuery'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Read':'E1M1AimPreRayMemory','Later':'E1M1AimPreRayMemory',
      'layout':'E1M1AimPreRayMemory','PayloadSafe':'E1M1AimPreRayMemory',
      'Initial':'E1M1AimPreRayCatalog','view':'E1M1AimQueryCatalog',
      'Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'traversal':'E1M1PathMapQuery','resolve':'E1M1ThingFinish'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimPreRayQuery\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimEntryQuery.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimEntryQuery.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-pre-ray-query';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimPreRayQuery'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Continuous P_AimLineAttack execution and center/right decision now take all machine-memory payload/catalog values before ray construction. Line/object/list payloads, portal/wall/actor catalogs and address guards are transported through actual setup. Shooter global is derived from initial EAX rather than falsely preserved. Generated query globals remain derived by the earlier setup join. No residual reached traversal-memory catalog, payload or callback contract is supplied in the combined theorem. Static layout views contain initial memory and substituted stack addresses only. Initial geometry/encoding/separation, valid shooter, positive distance, capacity, source success, arithmetic and pointer obligations remain; reachability and all three probes are not proved. No runtime, decoder, instruction-semantic or byte-range changes; emulator evidence inherited, not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: pre-ray memory contracts derive traversal catalogs/payloads and continuous query/decision; strict axiom audit.')
if __name__=='__main__':main()

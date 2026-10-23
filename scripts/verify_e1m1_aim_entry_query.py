#!/usr/bin/env python3
"""Certify the ray/setup join from aim entry to the production query result and controller decision."""
import argparse,json,re,subprocess
import verify_e1m1_aim_target_decision as previous
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimSetupEntry':['call','entry','globals'],
 'E1M1AimSetupLink':['ray','setup','execution'],
 'E1M1AimSetupCatalog':['initial','return_address'],
 'E1M1AimEntryQuery':['production','execution','decision']}
ENTRY_ARGS='q pick s f thing angle distance h shooter shooterValue positive profile xout yout okX okY common height statics scenes payloads separated callbackSafe cursorCall room portals walls who initial'
CONTRACTS=[
 ('E1M1AimSetupEntry','call','s thing angle distance ox oy geometry'),
 ('E1M1AimSetupEntry','entry','q s thing angle distance h'),
 ('E1M1AimSetupEntry','globals','s thing angle distance ox oy geometry'),
 ('E1M1AimSetupLink','ray','pc present'),
 ('E1M1AimSetupLink','setup','pc present'),
 ('E1M1AimSetupLink','execution','s f'),
 ('E1M1AimSetupCatalog','initial','q s scene shooter thing angle distance hits portals walls who h remaining'),
 ('E1M1AimSetupCatalog','return_address','q s stack safe'),
 ('E1M1AimEntryQuery','production','scene shooter thing angle distance path answer shooterValue positive traced processed'),
 ('E1M1AimEntryQuery','execution',ENTRY_ARGS),
 ('E1M1AimEntryQuery','decision',ENTRY_ARGS+' second returnSafe resume')]
NAMESPACE='Doom.Verification.ExtractedAimEntryQuery'

def declaration(module,name):
    source=(ROOT/f'Doom/Proofs/{module}.lean').read_text();a=source.index('theorem '+name+' ')
    decl=source[a:a+re.search(r' := by| :=\n',source[a:]).start()]
    owners={'Inputs':'E1M1AimSetupEntry','Remaining':'E1M1AimSetupCatalog',
      'Source':'E1M1AimQueryCaller','Portal':'E1M1AimCatalog',
      'traversal':'E1M1PathMapQuery','resolve':'E1M1ThingFinish'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimEntryQuery\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='\n'.join([
      'def linked := Doom.Verification.ExtractedAimTargetDecision.linked',
      'theorem linked_checked : linked=E1M1AimProgramLink.program :=',
      '  Doom.Verification.ExtractedAimTargetDecision.linked_checked',
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
    out=ROOT/'artifacts/e1m1-aim-entry-query';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimEntryQuery'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='One continuous authenticated execution from P_AimLineAttack entry through ray/setup, path traversal, ordered hits and return; returned target presence/slope agree with the full production aimLineAttack source result. Also appends the center/right decision with the landing PC derived from the protected original caller return word. Query entry geometry, map/epoch/stamps, callback arguments, range/eye/window/null target and nested return are derived from setup. Residual catalog, payload and callback protection contracts explicitly remain at the computed traversal boundary. Positive distance, valid shooter, source success, pointer validity, capacity and arithmetic contracts remain. No claim that all admitted E1M1 reachable states satisfy these, no complete three-probe controller, and no whole-game theorem. No runtime, decoder or instruction-semantic changes; inherited binary/emulator evidence, no rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: aim-entry/ray/query/return and single-probe decision; production source result and strict axiom audit.')
if __name__=='__main__':main()

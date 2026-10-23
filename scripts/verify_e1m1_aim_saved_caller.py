#!/usr/bin/env python3
"""Authenticate protected caller words through the exhaustive aiming loop."""
import argparse,json,re,subprocess
import verify_e1m1_aim_completed_return as previous
import verify_e1m1_aim_ordered_memory as ordered
import verify_e1m1_aim_actor_catalog as actor
import verify_e1m1_aim_actor_return as selected
ROOT,require=previous.ROOT,previous.require
pinned_data,extracted=previous.pinned_data,previous.extracted
HEADER=previous.HEADER
GROUPS={
 'E1M1AimSavedWords':['transport','from_cycle','selected_frame','selected'],
 'E1M1AimActorSavedCycle':['execution'],
 'E1M1AimHitSaved':['execution'],
 'E1M1AimOrderedSaved':['execution','initial'],
 'E1M1AimSavedCaller':['slot','cursor_safe','addresses','restores','execution']}
LOOP_ARGS=ordered.LOOP_ARGS.replace(' available ',' available watched ')
RESULT_ARGS=ordered.RESULT_ARGS.replace(' available ',' available watched ')+' protect'
CONTRACTS=[
 ('E1M1AimSavedWords','selected','selected_checked',selected.STOP_ARGS),
 ('E1M1AimActorSavedCycle','execution','actor_checked',actor.EXEC_ARGS),
 ('E1M1AimHitSaved','execution','hit_checked',ordered.HIT_ARGS),
 ('E1M1AimOrderedSaved','execution','loop_checked',LOOP_ARGS),
 ('E1M1AimOrderedSaved','initial','initial_checked',RESULT_ARGS),
 ('E1M1AimSavedCaller','addresses','addresses_checked','start finish base image stack first second'),
 ('E1M1AimSavedCaller','restores','restores_checked','start finish base image stack protect'),
 ('E1M1AimSavedCaller','execution','execution_checked','initial resolve start finish base steps answer run exit nonnull image stack protect first second')]

def declaration(module,name):
    # The earlier signature extractor qualifies the common loop vocabulary.
    decl=ordered.declaration(module,name)
    if module=='E1M1AimActorSavedCycle':
        decl=decl.replace('Doom.Proofs.E1M1AimHitMemory.Outcome','Doom.Proofs.E1M1AimActorCycle.Outcome')
        decl=decl.replace('Doom.Proofs.E1M1AimLineDispatch.dispatch','Doom.Proofs.E1M1AimActorDispatch.dispatch')
    owners={'Protect':'E1M1AimSavedWords','Preserved':'E1M1AimSavedWords',
        'Image':'E1M1AimSavedCaller','Restores':'E1M1AimSavedCaller','words':'E1M1AimSavedCaller','slots':'E1M1AimSavedCaller'}
    for word,owner in owners.items():
        decl=re.sub(r'(?<![.\w])'+word+r'\b','Doom.Proofs.'+owner+'.'+word,decl)
    return decl

NAMESPACE='Doom.Verification.ExtractedAimSavedCaller'
BASE_NAMES=['loop_program_checked','linked_checked']
def certificate(data,raw):
    source='import Doom.Proofs.E1M1AimSavedCaller\n'+previous.certificate(data,raw)
    source+='\nnamespace '+NAMESPACE+'\n'+HEADER
    source+='def loopProgram := Doom.Verification.ExtractedAimActorSelect.linked\n'
    source+='theorem loop_program_checked : loopProgram=E1M1AimActorSelect.program := Doom.Verification.ExtractedAimActorSelect.linked_checked\n'
    source+='def linked := Doom.Verification.ExtractedAimCompletedReturn.linked\n'
    source+='theorem linked_checked : linked=E1M1AimCompletedReturn.program := Doom.Verification.ExtractedAimCompletedReturn.linked_checked\n'
    for module,name,checked,args in CONTRACTS:
        decl=declaration(module,name).replace('theorem '+name,'theorem '+checked,1)
        decl=decl.replace('Doom.Proofs.E1M1AimActorSelect.program','loopProgram').replace('E1M1AimActorSelect.program','loopProgram')
        decl=decl.replace('Doom.Proofs.E1M1AimCompletedReturn.program','linked').replace('E1M1AimCompletedReturn.program','linked')
        source+='namespace '+module+'\n'+decl+' := by\n  '
        if 'loopProgram []' in decl: source+='rw [loop_program_checked] at *\n  '
        if 'linked []' in decl: source+='rw [linked_checked]\n  '
        source+='exact Doom.Proofs.'+module+'.'+name+' '+args+'\nend '+module+'\n'
    source+='\n'.join('#print axioms '+n for n in BASE_NAMES)+'\n'
    source+='\n'.join('#print axioms '+m+'.'+checked for m,_,checked,_ in CONTRACTS)+'\nend '+NAMESPACE+'\n'
    for m,names in GROUPS.items():source+='\n'.join('#print axioms Doom.Proofs.'+m+'.'+n for n in names)+'\n'
    return source

def audit(output):
    marker="'"+NAMESPACE+".loop_program_checked'"
    require(marker in output,'missing saved caller audit')
    before,rest=output.split(marker,1);previous.audit(before);rest=(marker+rest).strip()
    names=[NAMESPACE+'.'+n for n in BASE_NAMES]
    names+=[NAMESPACE+'.'+m+'.'+checked for m,_,checked,_ in CONTRACTS]
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
    out=ROOT/'artifacts/e1m1-aim-saved-caller';out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean';source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1AimSavedCaller'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr);audit(checked.stdout)
    report=dict(wad_sha256=mp['wad_sha256'],exe_sha256=profile['exe_sha256'],units=spec['units'],cells=len(data['cells']),
      scope='Protected fixed-address words survive every actor/line callback and the terminating exhaustive ordered loop. The saved caller image supplies entry-memory return addresses and saved values to the completed real return chain. Final ESP equals the chosen base remains an explicit endpoint premise; initial protection, representation and arithmetic availability remain premises. Collection/setup joining and whole aiming equivalence remain open. No new binary ranges or instruction semantics; no runtime changes. Emulator checks were not rerun.',
      emulator_evidence='artifacts/e1m1-aim-completed-return/validation.json')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: saved caller memory through exhaustive hit processing; strict axiom audit.')
if __name__=='__main__':main()

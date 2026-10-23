#!/usr/bin/env python3
"""Certify initialized intercept/counter transport through the first cell scans."""
import json
import re
import subprocess
import verify_e1m1_firing_advance as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalLineInterceptRegister': ['slot_address', 'saved_prologue', 'helper_apart', 'tested_saved', 'unwind_intercept', 'resume_intercept', 'finish_intercept', 'scratch_safe', 'crossing_intercept', 'rejected_intercept', 'entry_intercept', 'visit_intercept', 'dispatch_intercept', 'reject_intercept', 'saved_safe', 'step_intercept', 'run_intercept', 'finished_intercept'], 'E1M1ThingGridRegisters': ['slot_address', 'saved_prologue', 'entry_saved', 'finish_register', 'resume_register', 'visit_register', 'run_register', 'return_register', 'traversal_register', 'lookup_register'], 'E1M1FiringGridRegisters': ['caller_intercept', 'initialized', 'scan_intercept', 'boundary_register', 'firing_register', 'before_advance', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringGridRegisters\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.OriginalLineInterceptRegister.slot_address'"
    require(marker in output,'missing grid-register audit')
    before,rest=output.split(marker,1)
    previous.audit(before)
    rest=(marker+rest).strip()
    for module,names in GROUPS.items():
        for name in names:
            full='Doom.Proofs.'+module+'.'+name
            match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
            require(match is not None,'missing audit: '+full)
            axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
            require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms')
            rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    data,map_profile=pinned_data()
    spec,profile,raw=extracted()
    require(profile['exe_sha256']==map_profile['exe_sha256'],'executable profile mismatch')
    out=ROOT/'artifacts/e1m1-firing-grid-registers'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringGridRegisters'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. EBP survives the complete mixed line '
                      'scan; EBP and EDI survive every object callback, linked-list traversal and '
                      'iterator exit. The joined first-cell firing execution starts advancement '
                      'with the production-calculated X intercept and counter zero. Its counter '
                      'is then zero at endpoint exit or one at the next-cell gate. No extra '
                      'reached-register premise is added. Existing initial geometry, memory, '
                      'static separation, successful arithmetic, finite list and capacity '
                      'contracts remain. Y intercept, stride/direction/end locals still need '
                      'initialization transport; post-advance hit-array preservation, later cells, '
                      'outer production loop, clipping/damage, full query/tic and audiovisual '
                      'correspondence remain open. No production runtime code changed.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: initialized first-cell grid registers; strict transitive axiom audit.')


if __name__=='__main__':main()

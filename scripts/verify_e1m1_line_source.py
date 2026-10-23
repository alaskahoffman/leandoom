#!/usr/bin/env python3
"""Certify the mixed DOS line scan against the aiming source-loop fragment."""
import json
import re
import subprocess
import verify_e1m1_mixed_cell_walk as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1LineCollect': ['visit_step', 'collect_run'], 'E1M1LineSourceLoop': ['source_collect'], 'E1M1LineSourceScan': ['candidate_ids', 'source_result', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1LineSourceScan\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1LineCollect.visit_step'"
    require(marker in output,'missing line source-loop audit')
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
    out=ROOT/'artifacts/e1m1-line-source'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LineSourceScan'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The checked mixed '
                      'DOS line scan agrees with a proof-local restatement of the '
                      'production aiming line-cell loop at flags 3. The result '
                      'contains the full PathResult and updated seen array, with '
                      'raw ID order and repeats retained. Production lineIntercept '
                      'and appendIntercept are called directly. Signed-ID validation '
                      'and scene lookup precede duplicate rejection. The generic '
                      'source collector theorem preserves errors; the machine join '
                      'requires successful geometry/fractions, a valid scene lookup, '
                      'initial record/stamp representations and sufficient capacity. '
                      'This is not yet an equality for the actual Scene.pathTraverse '
                      'function: block logging, the enclosing grid loop and its '
                      'itinerary remain separate. Reachable-state discharge, general '
                      'budget sufficiency, intercept ordering, clipping and complete '
                      'query/tic remain open. Runtime and instruction semantics '
                      'are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: DOS line scan joined to aiming source-loop fragment; strict transitive axiom audit.')


if __name__=='__main__':main()

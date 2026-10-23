#!/usr/bin/env python3
"""Certify DOS collection against the exact live Lean grid loop."""
import json
import re
import subprocess
import verify_e1m1_generated_walk as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1TraversalLoop': ['live', 'live_aiming'], 'E1M1LoopReplay': ['object_loop', 'aiming_body', 'finish_pack', 'callback_step', 'body_pack', 'replay', 'walk_replay'], 'E1M1LiveWalk': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1LiveWalk\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1TraversalLoop.live'"
    require(marker in output,'missing live loop audit')
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
    out=ROOT/'artifacts/e1m1-live-walk'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LiveWalk'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Definition-level '
                      'equality exposes the actual loop in Scene.pathTraverse for '
                      'every flag setting, preserving initialization, failures and '
                      'later ordered visitation. At aiming flags, the exact live '
                      'Int32 loop equals logged collection on the generated route '
                      'for every finite budget, including errors and final numeric '
                      'state. Continuous DOS execution from the cell gate to loop '
                      'exit now agrees with that live source loop under the '
                      'existing legal-counter, scene/machine encoding, geometry, '
                      'separation and aggregate-capacity contracts. Query-entry '
                      'initialization still needs joining to this gate, and '
                      'reachable-state contracts/capacity remain to be discharged. '
                      'The source-fragment gap for grid collection is closed; DOS '
                      'ordered hit processing, aim clipping, query return/retry '
                      'and complete tic correspondence remain open. Runtime and '
                      'instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: DOS collection-loop execution agrees with the exact live Lean loop; strict transitive axiom audit.')


if __name__=='__main__':main()

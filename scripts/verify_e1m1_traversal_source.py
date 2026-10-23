#!/usr/bin/env python3
"""Certify the proved line collector inside the actual production traversal."""
import json
import re
import subprocess
import verify_e1m1_line_source as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1TraversalSource': ['live', 'aiming_flow_list', 'aiming_flow', 'live_aiming'], 'E1M1TraversalLineJoin': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1TraversalLineJoin\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1TraversalSource.live'"
    require(marker in output,'missing live traversal audit')
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
    out=ROOT/'artifacts/e1m1-traversal-source'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1TraversalLineJoin'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The actual production '
                      'Scene.pathTraverse is proved equal to a traversal exposing '
                      'its line callback for every flag setting and every input, '
                      'including errors and early returns. At aiming flags 3, that '
                      'callback is proved equal to the checked line-cell collector. '
                      'No validity or success premise is needed for these source '
                      'equalities. The existing authenticated DOS per-cell line '
                      'scan now produces this exact callback result under its '
                      'initial geometry, lookup, stamp, layout and capacity contracts. '
                      'This closes the isolated-source-fragment gap, but does not '
                      'prove the complete DOS traversal: actual machine itinerary '
                      'construction and composition with source block logging, '
                      'object loops and grid state remain. Reachable-state discharge, '
                      'general budget sufficiency, DOS ordered intercept processing, '
                      'aim clipping and complete query/tic remain open. Runtime '
                      'and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: checked line collector connected to actual production traversal; strict transitive axiom audit.')


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify query-entry initialization against the live aiming preparation."""
import json
import re
import subprocess
import verify_e1m1_live_walk as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1QueryInit': ['numeric', 'empty_collection', 'initial_visits'], 'E1M1QuerySource': ['live', 'prepare_ok', 'initialized']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1QuerySource\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1QueryInit.numeric'"
    require(marker in output,'missing query initialization audit')
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
    out=ROOT/'artifacts/e1m1-query-init'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1QuerySource'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Exact live aiming '
                      'query decomposition preserves profile checks, X then Y '
                      'calculation errors, collection and ordered visitation. '
                      'Query-entry DOS initialization derives all eleven numeric '
                      'fields, empty hit buffer and fresh visit history matching '
                      'source preparation, under explicit entry geometry, axis '
                      'success, separation and incremented-epoch freshness '
                      'contracts. No reached-gate memory premises are added. '
                      'Map/payload images and full initialization-to-loop '
                      'execution composition remain open, as do reachable '
                      'contracts, total capacity, DOS ordered hit processing, '
                      'aim clipping and whole-tic correspondence. Runtime and '
                      'instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: query initialization matches live source preparation; strict transitive axiom audit.')


if __name__=='__main__':main()

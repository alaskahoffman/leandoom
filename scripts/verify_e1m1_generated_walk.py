#!/usr/bin/env python3
"""Certify the numeric route and complete DOS collection-loop exit."""
import json
import re
import subprocess
import verify_e1m1_logged_walk as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1GridRoute': ['follows', 'nonempty', 'length_bound', 'source_eq', 'exits'], 'E1M1GeneratedWalk': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1GeneratedWalk\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1GridRoute.follows'"
    require(marker in output,'missing generated route audit')
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
    out=ROOT/'artifacts/e1m1-generated-walk'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1GeneratedWalk'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The numeric gate '
                      'state determines the visited cells; metadata cannot select '
                      'coordinates. Under a legal counter and its remaining budget, '
                      'the DOS continuation-PC route equals the endpoint/budget '
                      'route and reaches the original loop exit, including early '
                      'endpoints, repeated cells and stalls. The continuous DOS '
                      'execution agrees with logged source collection on that '
                      'generated route, preserving records, visit history and '
                      'initial images under one aggregate capacity bound. No '
                      'supplied itinerary or Follows premise remains in the join. '
                      'This still starts at the collection gate: query initialization '
                      'and equality to the actual enclosing production loop need '
                      'joining. Scene/machine encodings, candidate geometry, '
                      'arithmetic, separation and sufficient capacity remain '
                      'explicit. Ordered hit processing, clipping and full query/tic '
                      'remain open. Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: generated DOS route exits and agrees with logged source collection; strict transitive axiom audit.')


if __name__=='__main__':main()

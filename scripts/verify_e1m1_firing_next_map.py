#!/usr/bin/env python3
"""Certify persistent map data, lookup handoff and the two-cell remaining reserve."""
import json
import re
import subprocess
import verify_e1m1_firing_next_numeric as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1CellMapInvariant': ['frame_trans', 'transport', 'enabled', 'inputs', 'inside'], 'E1M1NextLookupFrame': ['prepared'], 'E1M1FiringNextMap': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextMap\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1CellMapInvariant.frame_trans'"
    require(marker in output,'missing persistent map audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-map'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextMap'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. A reusable immutable-read '
                      'frame transports the BLOCKMAP image, dimensions, pointers and '
                      'initialized line/object options. An arbitrary in-map gate executes '
                      'the original lookup in at most 30 instructions, preserving that '
                      'image, mixed records, exact reserve and visit history. The actual '
                      'continuous two-cell firing prefix now establishes the image and '
                      'protected-read frame and a reserve of 128 minus the two-cell '
                      'candidate bound. No reached capacity is newly assumed. Its '
                      'initialized numeric result and instruction bound are unchanged. '
                      'Initial encodings, fractions, layout, freshness and candidate '
                      'budget remain explicit. Repeated-cell callback/list invariant '
                      'closure, later-cell capacity, production outer-loop correspondence, '
                      'intercept ordering, clipping and full query/tic remain open. '
                      'Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: persistent map and remaining reserve joined; generic next lookup preserves both; strict transitive axiom audit.')


if __name__=='__main__':main()

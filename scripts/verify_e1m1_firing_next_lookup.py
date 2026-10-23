#!/usr/bin/env python3
"""Certify next-cell coordinates and the continuous second object-table lookup."""
import json
import re
import subprocess
import verify_e1m1_firing_next_things as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1NextCoordinates': ['scan_coordinate', 'suffix_coordinates'], 'E1M1NextThingLookup': ['contains_entry', 'execution'], 'E1M1FiringNextLookup': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextLookup\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1NextCoordinates.scan_coordinate'"
    require(marker in output,'missing firing next-lookup audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-lookup'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextLookup'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Grid-step coordinates survive '
                      'the next BLOCKMAP lookup, duplicate skip, complete line scan and '
                      'object CALL. The second object-table head is read from the intended '
                      'x + y*width cell; original firing-entry values and address separation '
                      'supply all reads. An empty list returns success to 0x2cab1 with '
                      'caller SP restored; a nonempty list reaches 0x2c5d2 with the actual '
                      'head pointer and saved callback 0x2c720. Mixed hits, their order, '
                      'cursor and updated visit stamps survive. Continuous post-sound '
                      'bound: 502 + 281*(first_line_count + next_tail_count) + '
                      '230*first_object_count. Initial encodings, successful fractions, '
                      'layout, freshness and two-cell budget remain explicit. Second '
                      'object-list execution, repeated-cell capacity/induction, production '
                      'outer-loop correspondence, clipping, damage and full query/tic '
                      'remain open. Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: next-cell coordinates and object-head lookup joined to firing prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

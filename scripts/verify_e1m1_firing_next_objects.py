#!/usr/bin/env python3
"""Certify the complete second object scan, including derived list image and capacity."""
import json
import re
import subprocess
import verify_e1m1_firing_next_lookup as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1NextObjectMemory': ['scan_size', 'read_word', 'caller_word'], 'E1M1FiringNextObjectImage': ['execution'], 'E1M1NextObjectTraversal': ['execution'], 'E1M1FiringNextObjects': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextObjects\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1NextObjectMemory.scan_size'"
    require(marker in output,'missing firing next-objects audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-objects'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextObjects'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The second object list image '
                      'derives from initial object coordinates, radii, linked-node words, '
                      'address separation and the freshly initialized trace. Its caller '
                      'word derives from the actual CALL. A four-list candidate budget '
                      'supplies capacity before execution. The existing finite-list '
                      'traversal handles both empty and nonempty lists, retains the '
                      'mixed collection and visited history, and returns success to '
                      '0x2cab1 at firing SP minus 112. The continuous post-sound bound '
                      'is 505 + 281*(first_line_count + next_tail_count) + '
                      '230*(first_object_count + next_object_count). The final collection '
                      'matches the selected production scene cell in its linked-ID order. '
                      'Initial encodings, fractions, layout, freshness and sufficient '
                      'candidate budget remain explicit. Repeated-cell invariants and '
                      'capacity, production outer-loop correspondence, ordered intercept '
                      'processing, clipping, damage and full query/tic remain open. '
                      'Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete second object scan joined to firing prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

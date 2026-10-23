#!/usr/bin/env python3
"""Certify object-grid preservation and the joined cell-return/advance boundary."""
import json
import re
import subprocess
import verify_e1m1_firing_next_objects as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1ObjectBoundary': ['preserved', 'observe'], 'E1M1CellBoundaryAdvance': ['frame', 'execution'], 'E1M1FiringNextBoundary': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextBoundary\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1ObjectBoundary.preserved'"
    require(marker in output,'missing firing next-boundary audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-boundary'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextBoundary'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Generic object traversal '
                      'preserves all four live grid registers, protected memory and '
                      'restores the caller stack. All eleven numeric grid fields match '
                      'the lookup state viewed at caller SP. A reusable successful-cell '
                      'return contract joins TEST/JZ and the actual grid advance in at '
                      'most 21 instructions, retaining mixed hits and visited history. '
                      'The continuous second-cell firing bound is 526 + '
                      '281*(first_line_count + next_tail_count) + '
                      '230*(first_object_count + next_object_count). Numeric output is '
                      'the original step of the actual second lookup caller view; '
                      'identifying that view with the production-initialized first '
                      'advance across the preceding line scan remains open. Protected '
                      'map/node reads survive object traversal and the advance. Initial '
                      'encodings, fractions, layout, freshness and candidate budget '
                      'remain explicit. Repeated-cell invariant closure, capacity, '
                      'production outer-loop correspondence, intercept ordering, clipping '
                      'and full query/tic remain open. Runtime and instruction semantics '
                      'are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: object grid-state preservation and cell return/advance joined; strict transitive axiom audit.')


if __name__=='__main__':main()

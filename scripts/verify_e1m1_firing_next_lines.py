#!/usr/bin/env python3
"""Certify continuous firing through the next cell remaining line scan."""
import json
import re
import subprocess
import verify_e1m1_firing_next_geometry as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1NextCursor': ['tail_address', 'tail_ids', 'firing_cursor'], 'E1M1NextLineScan': ['contains_scan', 'step_prefix', 'run_prefix', 'visit_layout', 'execution'], 'E1M1FiringNextLines': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextLines\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1NextCursor.tail_address'"
    require(marker in output,'missing firing next-lines audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-lines'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextLines'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The actual next-cell '
                      'BLOCKMAP offset derives the suffix cursor. Callback readiness '
                      'assembles the existing mixed-scan invariant using the line/object '
                      'resolver, preserving incoming object hits. Every remaining next-cell '
                      'line candidate and the sentinel return execute in the continuous '
                      'post-sound firing prefix under explicit initial layout and a '
                      'two-cell candidate budget. The bound is 474 + 281*(first_line_count '
                      '+ next_tail_count) + 230*first_object_count. The ordered collection '
                      'and updated visited history accompany the returned state; old '
                      'records remain an exact prefix of the final collection. Initial '
                      'encodings, arithmetic, separation and freshness remain explicit. '
                      'Restored caller observations, second-cell object scan, repeated-cell '
                      'capacity/induction, production outer-loop correspondence, clipping, '
                      'damage and full query/tic remain open. Runtime and instruction '
                      'semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: next-cell line scan joined to firing prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify finite in-map cell composition, shared capacity and the original limit."""
import json
import re
import subprocess
import verify_e1m1_cell_advance as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1CellWalkInvariant': ['caller_safe', 'images_transport', 'budget_tail'], 'E1M1CellWalk': ['one', 'execution'], 'E1M1CellWalkLimit': ['continuation', 'length_bound', 'exhausted']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1CellWalkLimit\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1CellWalkInvariant.caller_safe'"
    require(marker in output,'missing finite cell-walk audit')
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
    out=ROOT/'artifacts/e1m1-cell-walk'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1CellWalkLimit'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Any finite in-map '
                      'itinerary admitted by the original numeric step and intermediate '
                      'continuation tests composes into one continuous instruction prefix. '
                      'Future cell images are supplied in initial memory and transported '
                      'by execution; one initial sum-of-candidates budget bounds collection '
                      'growth throughout. The result retains records, visited history, '
                      'numeric grid state, final PC, protected reads and all supplied '
                      'images. Legal initial counters imply at most 64 minus the initial '
                      'count cells, including stalls; exhausting that budget implies '
                      'the original exit PC. Per-cell object results agree with production '
                      'sceneCell applied to checked mixed line-scan results. An admitted '
                      'in-map itinerary, initial images, static layout, callback '
                      'arithmetic and total candidate capacity remain explicit. This '
                      'does not construct every actual itinerary or prove that this '
                      'conservative budget suffices for every reachable query. Outside '
                      'cells, full production outer-line-loop equality, intercept '
                      'ordering, clipping, reachable-state discharge and whole query/tic '
                      'remain open. Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: finite in-map cell walk and original iteration limit joined; strict transitive axiom audit.')


if __name__=='__main__':main()

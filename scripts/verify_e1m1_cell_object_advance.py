#!/usr/bin/env python3
"""Certify arbitrary-cell object selection, traversal and numeric advancement."""
import json
import re
import subprocess
import verify_e1m1_firing_next_scene as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1CellObjectSelection': ['transport', 'read_word', 'frame', 'observe', 'caller_word'], 'E1M1CellObjectRun': ['execution'], 'E1M1CellObjectAdvance': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1CellObjectAdvance\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1CellObjectSelection.transport'"
    require(marker in output,'missing arbitrary object-cell audit')
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
    out=ROOT/'artifacts/e1m1-cell-object-advance'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1CellObjectAdvance'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. A persistent selection '
                      'image records the actual object-table pointer and selected head. '
                      'An arbitrary successful line return executes the enabled object '
                      'CALL, bounds/table lookup, complete empty or nonempty object list '
                      'and caller return in at most 31 + 230*nodes instructions. Fresh '
                      'callback/return words and persistent scene data derive readiness. '
                      'The joined success test and original grid advance take at most '
                      '52 + 230*nodes instructions. Production scene-cell hits, numeric '
                      'step/control, visited history, protected reads, map/scene/selection '
                      'images and conservative remaining reserve are retained. The '
                      'pre-object line-return contract, selected scene IDs, layouts, '
                      'arithmetic and incoming capacity remain explicit. Generic line '
                      'phase composition, initial/reachable-state discharge, repeated-cell '
                      'capacity/induction, ordering, clipping and full query/tic remain '
                      'open. Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: arbitrary-cell object selection/traversal/advance joined; strict transitive axiom audit.')


if __name__=='__main__':main()

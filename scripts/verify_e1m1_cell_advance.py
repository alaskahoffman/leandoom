#!/usr/bin/env python3
"""Certify an in-map gate through both scans and original numeric advancement."""
import json
import re
import subprocess
import verify_e1m1_cell_object_advance as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1CellLineBoundary': ['lookup_view', 'frame', 'observe'], 'E1M1CellScanAdvance': ['execution'], 'E1M1CellAdvance': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1CellAdvance\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1CellLineBoundary.lookup_view'"
    require(marker in output,'missing in-map cell audit')
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
    out=ROOT/'artifacts/e1m1-cell-advance'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1CellAdvance'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. An enabled in-map gate '
                      'executes actual BLOCKMAP lookup, the complete mixed line scan, '
                      'object-table lookup, complete object list and original grid step '
                      'in at most 89 + 281*lines + 230*nodes instructions. The line '
                      'scan entry, callback and return words, restored grid counter, '
                      'object head and persistent images are derived from execution. '
                      'The output retains numeric step/control, updated visited history, '
                      'map/scene/selection images, protected reads and conservative '
                      'remaining capacity. Object hits agree with production sceneCell '
                      'applied to the checked mixed line-scan result. This does not '
                      'yet identify that result with the production outer line loop. '
                      'Initial encodings, layouts, callback arithmetic, selected scene '
                      'IDs and whole-cell capacity remain explicit. Repeated-cell '
                      'capacity/induction, outside/exit paths, ordering, clipping, '
                      'reachable-state discharge and full query/tic remain open. '
                      'Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: in-map gate/line/object/advance joined; strict transitive axiom audit.')


if __name__=='__main__':main()

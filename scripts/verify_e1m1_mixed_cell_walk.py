#!/usr/bin/env python3
"""Certify both out-of-map returns and mixed inside/outside cell composition."""
import json
import re
import subprocess
import verify_e1m1_cell_walk as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1OutsideLine': ['memory', 'read_word', 'register', 'execution'], 'E1M1OutsideCell': ['state_reads', 'objects', 'execution'], 'E1M1MixedCellWalk': ['images_transport', 'one', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1MixedCellWalk\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1OutsideLine.memory'"
    require(marker in output,'missing mixed cell-walk audit')
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
    out=ROOT/'artifacts/e1m1-mixed-cell-walk'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1MixedCellWalk'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The original line '
                      'and object bounds checks reject out-of-map cells and return '
                      'success through their actual callers. No cell list, object head '
                      'or callback payload is required there. The complete outside '
                      'path takes at most 71 modeled instructions, preserves collected '
                      'records and visited history, and executes the original grid step. '
                      'Mixed finite inside/outside itineraries now compose continuously '
                      'from initial images and one candidate budget; outside cells '
                      'spend zero collection budget but still consume iterations. '
                      'The existing Follows relation, original final PC and legal '
                      '64-iteration limit apply without changes. Initial encodings, '
                      'static layouts, callback arithmetic, a numerically admitted '
                      'itinerary and sufficient aggregate inside-cell capacity remain '
                      'explicit. Actual itinerary construction, general budget '
                      'sufficiency, production outer-line-loop equality, intercept '
                      'ordering, clipping, reachable-state discharge and whole '
                      'query/tic remain open. Runtime and instruction semantics '
                      'are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: outside bounds returns and mixed cell traversal joined; strict transitive axiom audit.')


if __name__=='__main__':main()

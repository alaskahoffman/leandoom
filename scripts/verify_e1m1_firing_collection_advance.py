#!/usr/bin/env python3
"""Certify hit collection preservation and the next-cell boundary."""
import json
import re
import subprocess
import verify_e1m1_firing_grid_state as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1AdvanceCollection': ['memory', 'frame', 'collection', 'counter', 'next_gate_iff', 'continuing_index', 'iteration'], 'E1M1FiringCollectionAdvance': ['execution', 'next_cell']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringCollectionAdvance\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1AdvanceCollection.memory'"
    require(marker in output,'missing collection-advance audit')
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
    out=ROOT/'artifacts/e1m1-firing-collection-advance'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringCollectionAdvance'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Grid advancement preserves all '
                      'ordered intercept records, the exact cursor and the unchanged capacity '
                      'reserve. Its only possible write is the Y-intercept local, protected '
                      'by the existing initial layout contract; no new reached-memory premise '
                      'is added. A reusable end-of-cell execution theorem combines this '
                      'collection invariant with numeric state, stack and the natural iteration '
                      'index, including endpoint, stall and final-budget branches. Continuation '
                      'derives a legal next index. The firing prefix retains the first scene '
                      'cell collection after advancement and, for a nonendpoint cell, reaches '
                      'the next gate with count one. Next-cell lookup/scan inputs, mutable '
                      'visit-stamp transport and traversal-wide capacity are still open, as '
                      'are the outer source loop, clipping/damage and complete query/tic '
                      'correspondence. Existing initial geometry, memory, layout, arithmetic '
                      'and finite scene/list contracts remain. Runtime code is unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: first-cell advancement with retained ordered hits; strict transitive axiom audit.')


if __name__=='__main__':main()

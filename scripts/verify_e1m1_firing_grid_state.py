#!/usr/bin/env python3
"""Certify complete initialized numeric grid state through the first cell scans."""
import json
import re
import subprocess
import verify_e1m1_firing_grid_registers as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1GridLocals': ['below', 'scan_safe', 'thing_safe', 'endpoints'], 'E1M1FiringGridState': ['of_ready', 'transport', 'grid_stack', 'initial_observe', 'caller_local', 'boundary_local', 'firing_local', 'before_observe', 'execution', 'production_axis']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringGridState\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1GridLocals.below'"
    require(marker in output,'missing grid-state audit')
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
    out=ROOT/'artifacts/e1m1-firing-grid-state'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringGridState'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The complete eleven-field first '
                      'grid-step observation is connected to production path initialization, '
                      'including all seven stack locals and both endpoints. Line and object '
                      'scans preserve these locals under an explicit initial address-only '
                      'stamp/intercept-array separation contract. All callback stack separation '
                      'is derived, including modular wraparound. The common post-sound firing '
                      'prefix executes the first advance from that initialized state within '
                      '427+281*line_count+230*object_count instructions. The axis fragment '
                      'matches the signed/wrapping production expression. Existing initial '
                      'geometry, memory, successful arithmetic, layout, finite list/scene and '
                      'capacity contracts remain. Post-advance hit-array preservation, '
                      'later cells, traversal-wide capacity, the outer production loop, '
                      'clipping/damage and full query/tic/audiovisual correspondence remain '
                      'open. No production runtime code changed.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: complete initialized first-cell grid state; strict transitive axiom audit.')


if __name__=='__main__':main()

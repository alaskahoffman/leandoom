#!/usr/bin/env python3
"""Certify firing through first-cell scans and next-cell lookup."""
import json
import re
import subprocess
import verify_e1m1_next_cell_scan as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1FiringCellMemory': ['object_frame', 'firing_frame', 'after_lines_frame'], 'E1M1FiringMapState': ['caller_safe', 'flag_safe', 'flag_word', 'enabled', 'map'], 'E1M1FiringNextScan': ['caller_array', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextScan\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1FiringCellMemory.object_frame'"
    require(marker in output,'missing firing next-scan audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-scan'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextScan'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Both post-sound firing entries '
                      'now execute the complete first line/object cell, numeric grid step and '
                      'next in-map cell lookup in one prefix, within 457 + 281*line_count + '
                      '230*object_count modeled instructions. The selected next list and SP '
                      'are derived, and the first scene cell ordered hits/cursor survive with '
                      'zero reserve. Map values and both enable bits are transported from '
                      'their actual initialization; extra premises are initial address '
                      'separation, not reached memory values. A reusable frame starts after '
                      'the line scan to preserve its modified stamps through objects. '
                      'The visited-set relation is not yet joined to this prefix. Next-cell '
                      'callback readiness, cumulative capacity, repeated-cell induction, '
                      'aim clipping, damage and complete query/tic remain open. Runtime '
                      'and machine instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: firing through next-cell lookup with retained hits; strict transitive axiom audit.')


if __name__=='__main__':main()

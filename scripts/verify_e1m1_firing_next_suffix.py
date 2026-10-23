#!/usr/bin/env python3
"""Certify the firing next-cell duplicate skip, exact suffix and capacity bound."""
import json
import re
import subprocess
import verify_e1m1_firing_visited_next as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1DuplicateSuffix': ['contains_resume', 'skip', 'address', 'scan_tail'], 'E1M1CellCapacity': ['collect_bound', 'scene_bound', 'reserve', 'suffix_reserve'], 'E1M1FiringNextSuffix': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextSuffix\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1DuplicateSuffix.contains_resume'"
    require(marker in output,'missing firing next-suffix audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-suffix'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextSuffix'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The continuous firing prefix '
                      'executes the next cell leading-zero duplicate skip, advancing its '
                      'cursor by two bytes with all memory unchanged. ScanWords describes '
                      'exactly the remaining list and sentinel, not a fresh BLOCKMAP list. '
                      'The instruction bound is 467 + 281*line_count + 230*object_count. '
                      'Ordered hits and visited history survive. A proved first-cell '
                      'candidate bound derives reserve 128-(line_count+object_count); '
                      'using it for remaining candidates requires an explicit two-cell '
                      'budget. This is not a traversal-wide capacity theorem. Initial '
                      'memory encodings, arithmetic, separation and freshness remain '
                      'explicit. Next-cell callbacks, repeated-cell induction, production '
                      'outer-loop correspondence, aim clipping, damage and full query/tic '
                      'remain open. Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: duplicate skip, exact suffix and capacity joined to firing prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

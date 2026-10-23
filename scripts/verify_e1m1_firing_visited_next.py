#!/usr/bin/env python3
"""Certify updated line-visit history through the firing next-cell prefix."""
import json
import re
import subprocess
import verify_e1m1_firing_next_scan as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalLineVisitedRun': ['mark_size', 'mark_keeps', 'first_marked', 'run_represents', 'finished_represents'], 'E1M1FiringLineVisits': ['seen_size', 'seen_zero', 'visit_layout', 'scan_seen', 'fresh_scan'], 'E1M1FiringVisitedNext': ['next_safe', 'leading_duplicate', 'before_seen', 'next_seen', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringVisitedNext\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.OriginalLineVisitedRun.mark_size'"
    require(marker in output,'missing firing visited-next audit')
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
    out=ROOT/'artifacts/e1m1-firing-visited-next'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringVisitedNext'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The continuing first line '
                      'scan marks its candidate IDs, including repeats and leading linedef '
                      'zero. Starting from all-false bits requires explicit firing-entry '
                      'freshness against the incremented epoch. The derived stamp/bit '
                      'relation survives the sentinel return, complete object scan, grid '
                      'advance and next lookup. It joins the 457 + 281*line_count + '
                      '230*object_count continuous firing prefix with selected next list '
                      'and retained hits. The next leading-zero duplicate branch is proved '
                      'true; its instructions are not executed by this prefix. Initial '
                      'setup/stamp/tail address separation and freshness remain explicit. '
                      'Next-cell callback readiness, cumulative capacity, repeated-cell '
                      'induction, source outer-loop correspondence, aim clipping, damage '
                      'and full query/tic remain open. Runtime and instruction semantics '
                      'are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: visited-line history joined to firing next-cell prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

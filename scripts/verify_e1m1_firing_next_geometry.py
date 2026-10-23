#!/usr/bin/env python3
"""Certify next-cell callback readiness derived from firing-entry line data."""
import json
import re
import subprocess
import verify_e1m1_firing_next_suffix as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1NextCallbackMemory': ['line_words', 'caller_callback', 'next_frame', 'firing_frame', 'initialized_frame', 'trace_words', 'active', 'callback_word'], 'E1M1NextCallbackReady': ['rejection', 'crossing'], 'E1M1FiringNextGeometry': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextGeometry\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1NextCallbackMemory.line_words'"
    require(marker in output,'missing firing next-geometry audit')
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
    out=ROOT/'artifacts/e1m1-firing-next-geometry'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextGeometry'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Next-cell line and vertex '
                      'data are transported from firing entry through both first-cell '
                      'scans, grid advancement and lookup. The initialized trace and '
                      'autoaim active flag are preserved from initialization rather than '
                      'assumed to match old memory. CALL/prologue derive the callback '
                      'word. The exact reached suffix gains indexed callback geometry, '
                      'back-sector tests, production crossing fractions and storage '
                      'layout; rejection and crossing contracts follow. These facts join '
                      'the same 467 + 281*line_count + 230*object_count firing prefix, '
                      'retaining ordered hits, reserve and visited history. Initial '
                      'encodings, arithmetic and address separation remain explicit. '
                      'Indexed templates still need the scan invariant to reach actual '
                      'later callbacks; no additional callback is executed here. Mixed '
                      'line/object resolver assembly, cumulative capacity, repeated-cell '
                      'induction, production outer loop, clipping, damage and full '
                      'query/tic remain open. Runtime and instruction semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: next-cell callback readiness joined to firing prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify continuous DOS initialization and live aiming collection."""
import json
import re
import subprocess
import verify_e1m1_query_init as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1QueryImages': ['globals', 'map', 'cell', 'images'], 'E1M1QueryPrefix': ['contains_grid', 'execution'], 'E1M1QueryCollection': ['state', 'query_tail', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1QueryCollection\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1QueryImages.globals'"
    require(marker in output,'missing query collection audit')
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
    out=ROOT/'artifacts/e1m1-query-collection'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1QueryCollection'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. Continuous '
                      'execution from P_PathTraverse entry through collection '
                      'exit agrees with the actual source aiming collection. '
                      'The complete numeric/map/buffer/visit invariant and all '
                      'used callback images are derived from entry memory; '
                      'initialization supplies trace and active globals. '
                      'The remaining live query is exactly its ordered visitor '
                      'tail. Contracts still require profile, geometry, axis '
                      'success, encoding, freshness, separation, callback '
                      'arithmetic and total capacity. These are not yet proved '
                      'for every reachable query. DOS ordered hit processing, '
                      'aim clipping, query return/retry and whole-tic parity '
                      'remain open. Runtime and instruction semantics unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: continuous DOS query initialization and collection match the live source; strict transitive axiom audit.')


if __name__=='__main__':main()

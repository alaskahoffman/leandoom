#!/usr/bin/env python3
"""Certify grid advancement through arbitrary next-cell lookup."""
import json
import re
import subprocess
import verify_e1m1_firing_collection_advance as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1NextCellMemory': ['stack', 'caller_safe', 'caller_frame', 'frame', 'enabled', 'visits', 'image', 'collection', 'map'], 'E1M1NextCellScan': ['contains_caller', 'inside', 'outside', 'scan_invariants']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1NextCellScan\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1NextCellMemory.stack'"
    require(marker in output,'missing next-cell scan audit')
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
    out=ROOT/'artifacts/e1m1-next-cell-scan'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NextCellScan'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. An arbitrary continuing grid '
                      'step joins the next in-map cell lookup within 49 instructions, or the '
                      'out-of-map line return and thing gate within 43. Coordinates derive '
                      'from the numeric step. Map, dimension and enable facts are transported '
                      'from before advancement. The same visited set/epoch, raw map words, '
                      'ordered hits, cursor and unchanged reserve survive advancement and '
                      'lookup under explicit pre-step separation. These are reusable boundary '
                      'contracts, not a joined firing-through-second-scan theorem. Deriving '
                      'these memory/visit contracts after earlier scans, next-cell callback '
                      'readiness, cumulative capacity, outer-loop induction and whole-query '
                      'correspondence remain open. Runtime code is unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: next-cell lookup with retained scan invariants; strict transitive axiom audit.')


if __name__=='__main__':main()

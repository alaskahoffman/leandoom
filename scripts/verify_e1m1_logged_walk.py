#!/usr/bin/env python3
"""Certify source collection with logs across the admitted DOS cell walk."""
import json
import re
import subprocess
import verify_e1m1_traversal_source as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1CellLineSource': ['lines'], 'E1M1CollectionLog': ['append_log', 'line_log_list', 'line_log', 'state_log'], 'E1M1LoggedCell': ['one'], 'E1M1LoggedWalk': ['execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1LoggedWalk\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1CellLineSource.lines'"
    require(marker in output,'missing logged collection audit')
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
    out=ROOT/'artifacts/e1m1-logged-walk'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1LoggedWalk'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. At each real cell '
                      'gate, initial map/payload images derive the source line '
                      'collector result without reached-callback assumptions. '
                      'The scene line-ID and geometry relation is explicit. Logging '
                      'commutes with the line collector, including errors. A whole '
                      'inside/outside cell agrees with source line-before-object '
                      'collection and both block log entries. Finite admitted '
                      'itineraries compose into a continuous DOS prefix and an '
                      'executable source collection result, retaining the complete '
                      'PathResult, visited history, numeric step, final PC, initial '
                      'images and one total capacity budget. The itinerary is still '
                      'supplied with Follows; this does not construct all actual '
                      'queries or identify this finite replay with the complete '
                      'production grid loop. Reachable encodings, source scene '
                      'relations, arithmetic, separation and sufficient capacity '
                      'remain explicit. Actual itinerary construction and the '
                      'source controller join, DOS ordered hit processing, clipping '
                      'and full query/tic remain open. Runtime and instruction '
                      'semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: admitted DOS walk agrees with logged source collection; strict transitive axiom audit.')


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Certify query-entry geometry and its connection to the firing/scan prefix."""
import json
import re
import subprocess
import verify_e1m1_path_map_firing as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['samples_of_tables', 'selected_samples', 'endpoint', 'ray_registers', 'ray_frame',
          'setup_inputs', 'path_inputs', 'query_path_correspondence', 'first_scan_execution']
NAMES = ['geometry_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1AimGeometry\n'+previous.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedAimGeometry
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1AimGeometry
 theorem geometry_checked (s : X86Memory.State) (thing : Collision.SolidThing)
    (angle : Angle) (distance ox oy : Fixed) (h : Inputs s thing angle distance ox oy) :
    OriginalPathInit.Inputs (E1M1PathMapQuery.traversal s).core ox oy thing.x thing.y
      (thing.attackEndpoint angle distance).1 (thing.attackEndpoint angle distance).2 :=
  path_inputs s thing angle distance ox oy h
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1AimGeometry.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedAimGeometry\n'


def audit(output):
    marker="'Doom.Verification.ExtractedAimGeometry.geometry_checked'"
    require(marker in output, 'missing geometry certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedAimGeometry.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1AimGeometry.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-aim-geometry'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1AimGeometry'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Query-entry shooter words, selected sine/cosine values, origins and layout derive '
                        'aim setup and traversal-init geometry, with no intermediate coordinate or endpoint '
                        'assumption. The shared firing-to-scan join uses this geometry at first-query entry '
                        'and map data at post-sound entry. Shooter/angle/table transport through earlier firing, '
                        'loader reachability, visited state, callback storage, later-cell capacity and '
                        'complete-query/tic correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: selected ray samples, query-to-path geometry and shared scan join; strict axiom audit.')


if __name__ == '__main__':
    main()

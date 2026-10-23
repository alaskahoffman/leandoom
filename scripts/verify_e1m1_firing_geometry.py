#!/usr/bin/env python3
"""Certify post-sound shooter/table transport and the firing/scan prefix."""
import json
import re
import subprocess
import verify_e1m1_aim_geometry as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['flashed_player', 'flashed_frame', 'aim_frame', 'aim_actor', 'first_request',
          'aim_layout', 'path_writes', 'flag_layout', 'path_layout', 'transport', 'query_geometry', 'first_path_correspondence', 'first_scan_execution']
NAMES = ['geometry_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringGeometry\n'+previous.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedFiringGeometry
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1FiringGeometry
theorem geometry_checked (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (h : Inputs gun s actor thing angle ox oy) :
    E1M1AimGeometry.Inputs (E1M1BulletAim.firstQuery gun s).core thing angle (Fixed.ofInt 1024) ox oy :=
  query_geometry gun s actor thing angle ox oy h
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1FiringGeometry.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedFiringGeometry\n'


def audit(output):
    marker="'Doom.Verification.ExtractedFiringGeometry.geometry_checked'"
    require(marker in output, 'missing geometry certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedFiringGeometry.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1FiringGeometry.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-firing-geometry'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1FiringGeometry'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Post-sound shooter pointer, actor angle/coordinates/height, selected table samples '
                        'and origins survive the actual firing/slope setup and derive query-entry geometry. '
                        'Map and geometry contracts now share the post-sound firing boundary for both weapons. '
                        'The <=223-instruction path initialization and <=368-instruction first-scan join no '
                        'longer assume intermediate geometric encodings. Loader linkage, earlier sound, '
                        'line/visited/callback relations, later-cell capacity and full-query/tic equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: post-sound shooter/table geometry and shared scan join; strict axiom audit.')


if __name__ == '__main__':
    main()

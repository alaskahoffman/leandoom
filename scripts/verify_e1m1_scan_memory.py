#!/usr/bin/env python3
"""Certify first-scan line memory, initialized trace and visit epoch transport."""
import json
import re
import subprocess
import verify_e1m1_firing_geometry as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['caller_frame', 'initialized_frame', 'traversal_frame', 'firing_frame', 'firing_line', 'before_init_frame', 'firing_stack', 'firing_initialized_frame', 'firing_trace', 'firing_epoch', 'seen_iff', 'firing_seen']
NAMES = ['frame_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ScanMemory\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedScanMemory
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1ScanMemory
theorem frame_checked (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy) (a : Word)
    (safe : E1M1PathMapFiring.Safe gun s a) :
    load32 (firstScan gun s).core.memory a=load32 s.memory a :=
  firing_frame gun s actor thing angle ox oy geometry a safe
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ScanMemory.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedScanMemory\n'


def audit(output):
    marker="'Doom.Verification.ExtractedScanMemory.frame_checked'"
    require(marker in output, 'missing scan-memory certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedScanMemory.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1ScanMemory.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = previous.previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-scan-memory'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ScanMemory'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Protected words and loaded line/vertex data survive the actual post-sound '
                        'firing prefix through first-scan setup. Initialized trace words and the incremented '
                        '32-bit visit epoch survive later writes. Initial per-line duplicate checks are related '
                        'to post-sound stamps, without assuming freshness or excluding counter wraparound. '
                        'These are contracts on the first-scan state expression; the existing execution join '
                        'still requires weapon, map, successful-axis and inside-cell premises. '
                        'Callback storage, scan-wide visited-set evolution, loaded-map linkage, later-cell '
                        'capacity and full-query/tic equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: first-scan memory, trace and initial visited stamps; strict axiom audit.')


if __name__ == '__main__':
    main()

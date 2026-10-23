#!/usr/bin/env python3
"""Certify firing-entry geometry and intercept-storage contracts for the line scan."""
import json
import re
import subprocess
import verify_original_line_visits as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['caller_stack', 'firing_stack', 'view_stack', 'side_safe', 'scratch_safe',
          'callback_geometry', 'rejection_inputs', 'crossing_inputs', 'storage_layout',
          'first_line_geometry']
NAMES = ['crossing_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ScanGeometry\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedScanGeometry
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1ScanGeometry
theorem crossing_checked (s : X86Memory.State) (trace : Collision.Divline)
    (line : Collision.Line) (p v w : Word) (geometry : Geometry s trace line p v w)
    (crosses : OriginalLineSecondPoint.firstSide trace line≠OriginalLineSecondPoint.lastSide trace line) :
    OriginalLineCrossing.Inputs s trace line p v w :=
  crossing_inputs s trace line p v w geometry crosses
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ScanGeometry.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedScanGeometry\n'


def audit(output):
    marker="'Doom.Verification.ExtractedScanGeometry.crossing_checked'"
    require(marker in output, 'missing scan-geometry certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedScanGeometry.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1ScanGeometry.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def pinned_data():
    return previous.previous.previous.previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()


def main():
    data, map_profile = pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-scan-geometry'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ScanGeometry'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Both weapons share a firing-entry-to-first-scan instruction prefix. '
                        'Initial line data and initialized trace supply the indexed callback geometry '
                        'templates for crossing and rejection. The scan SP and callback SP are derived, '
                        'and initial byte separation supplies intercept-storage layout. '
                        'This does not assert execution of every indexed callback: mixed-scan readiness, '
                        'tail fractions/flags, protected words, stamp layout and freshness still need '
                        'assembly at firing entry. Complete query/tic and graphical parity remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: firing-to-scan geometry and intercept-storage layout; strict axiom audit.')


if __name__ == '__main__':
    main()

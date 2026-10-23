#!/usr/bin/env python3
"""Certify assembled aiming line-scan contracts and execution."""
import json
import re
import subprocess
import verify_e1m1_scan_geometry as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['firing_active', 'firing_back', 'candidate_continues', 'fixed_member', 'list_member', 'read_member', 'protection', 'initial', 'visit_layout', 'scan_execution', 'through_sentinel']
NAMES = ['continuation_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ScanContracts\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedScanContracts
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1ScanContracts
theorem continuation_checked (trace : Collision.Divline) (lines : Word) (id : Nat) (d : LineData) :
    (candidate trace lines id d).Continues :=
  candidate_continues trace lines id d
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ScanContracts.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedScanContracts\n'


def audit(output):
    marker="'Doom.Verification.ExtractedScanContracts.continuation_checked'"
    require(marker in output, 'missing scan-contracts certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedScanContracts.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1ScanContracts.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def pinned_data():
    return previous.pinned_data()


def main():
    data, map_profile = pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-scan-contracts'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ScanContracts'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Original firing setup supplies zero early-out flags; back-sector encoding is transported. '
                        'A generated read set and initial byte separation assemble the complete mixed-scan '
                        'contract, including callback geometry, fractions, storage and mutable-stamp layout. '
                        'The assembled contract is connected to bounded instruction execution, visited arrays, '
                        'and the continuing scan with sentinel return. Initial geometry, successful fractions, '
                        'capacity and memory representation remain explicit. The final common firing-entry '
                        'wrapper, loader/reachability/freshness, later cells, complete query/tic and graphical '
                        'parity remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: assembled aiming scan, visited arrays and sentinel return; strict axiom audit.')


if __name__ == '__main__':
    main()

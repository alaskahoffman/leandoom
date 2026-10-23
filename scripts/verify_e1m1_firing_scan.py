#!/usr/bin/env python3
"""Certify the common firing-entry to first-cell scan connection."""
import json
import re
import subprocess
import verify_e1m1_scan_contracts as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['caller_target', 'caller_cursor', 'firing_program', 'contains_firing', 'boundary', 'initial', 'scan_return', 'firing_through_sentinel']
NAMES = ['program_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringScan\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedFiringScan
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1FiringScan
theorem program_checked (pc : Nat) :
    E1M1PathMapCaller.firingProgram pc=E1M1LineCell.program pc :=
  firing_program pc
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1FiringScan.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedFiringScan\n'


def audit(output):
    marker="'Doom.Verification.ExtractedFiringScan.program_checked'"
    require(marker in output, 'missing firing-scan certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedFiringScan.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1FiringScan.'+n for n in PROOFS]:
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
    out = ROOT/'artifacts/e1m1-firing-scan'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1FiringScan'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Common post-sound firing-entry contracts derive the actual scan cursor, saved callback, '
                        'geometry and initialized empty intercept collection for pistol and shotgun. '
                        'A continuous decoded original-instruction prefix reaches the first-cell sentinel '
                        'return with ordered intercept encoding, bounded by 375+281*list_length. '
                        'Initial memory encodings, separation and successful computations remain explicit. '
                        'Loaded-map/reachability/freshness, later cells, things, clipping, complete query/tic '
                        'and audiovisual parity remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: continuous firing to first-cell sentinel return; strict axiom audit.')


if __name__ == '__main__':
    main()

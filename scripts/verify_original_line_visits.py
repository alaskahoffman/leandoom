#!/usr/bin/env python3
"""Certify DOS stamp updates and the mixed scan visited-array relation."""
import json
import re
import subprocess
import verify_e1m1_scan_memory as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['stamps_apart', 'set_already', 'represents_update', 'fresh_represents', 'firing_represents', 'selected_stamp', 'stamp_protected', 'entry_word', 'step_stamps', 'step_epoch', 'duplicate_iff', 'step_represents', 'scan_represents', 'scan_execution']
NAMES = ['array_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.OriginalLineVisits\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedLineVisits
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control OriginalLineVisits
theorem array_checked (memory : Memory) (lines epoch : Word) (count : Nat)
    (counter : load32 memory 0x13580=epoch)
    (fresh : ∀ j<count, load32 memory (stamp lines j)≠epoch) :
    Represents memory lines epoch (Array.replicate count false) :=
  fresh_represents memory lines epoch count counter fresh
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.OriginalLineVisits.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineVisits\n'


def audit(output):
    marker="'Doom.Verification.ExtractedLineVisits.array_checked'"
    require(marker in output, 'missing visited-array certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedLineVisits.'+n for n in NAMES]+[
            'Doom.Proofs.OriginalLineVisits.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = previous.previous.previous.previous.setup.setup.caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/original-line-visits'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.OriginalLineVisits'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Original callback stamps correspond to the production Boolean-array set! operation '
                        'through a bounded mixed scan, with repeated IDs, rejection, negative fractions and '
                        'early stops. Initial layout plus the existing scan invariant derive all reached stamp '
                        'protection. The array relation accompanies the original instruction prefix. '
                        'The firing-entry relation is connected; all-false initialization requires explicit '
                        'freshness, including at epoch wraparound. Assembly of the concrete firing-to-scan '
                        'geometry/storage contract, freshness/reachability, later cells, the complete query '
                        'and whole-tic equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: callback stamps, repeated-ID visited arrays and scan execution; strict axiom audit.')


if __name__ == '__main__':
    main()

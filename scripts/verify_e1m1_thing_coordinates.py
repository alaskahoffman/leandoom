#!/usr/bin/env python3
"""Certify coordinate restoration and the intended cell at the original thing CALL."""
import json
import re
import subprocess
import verify_e1m1_thing_gate as previous
ROOT, require = previous.ROOT, previous.require
GENERIC = ['slot_address', 'saved_prologue', 'helper_apart', 'tested_saved', 'unwind_coordinate', 'resume_coordinate', 'finish_coordinate', 'scratch_safe', 'crossing_coordinate', 'rejected_coordinate', 'entry_coordinate', 'visit_coordinate', 'dispatch_coordinate', 'reject_coordinate', 'saved_safe', 'step_coordinate', 'run_coordinate', 'finished_coordinate']
PROOFS = ['caller_coordinate', 'first_coordinates', 'scan_coordinate', 'call_coordinates', 'firing_call']
NAMES = ['coordinates_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingCoordinates\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingCoordinates
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1ThingCoordinates
theorem coordinates_checked (s : X86Memory.State) (x : Bool) :
    (E1M1PathMapCaller.scan s).core.regs (OriginalLineCoordinates.register x)=
      s.regs (OriginalLineCoordinates.register x) := caller_coordinate s x
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.OriginalLineCoordinates.'+n for n in GENERIC)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ThingCoordinates.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedThingCoordinates\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingCoordinates.coordinates_checked'"
    require(marker in output, 'missing thing-coordinate certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingCoordinates.'+n for n in NAMES]+[
            'Doom.Proofs.OriginalLineCoordinates.'+n for n in GENERIC]+[
            'Doom.Proofs.E1M1ThingCoordinates.'+n for n in PROOFS]:
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
    out = ROOT/'artifacts/e1m1-thing-coordinates'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingCoordinates'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='ECX/ESI are saved, protected and restored across both line callback outcomes and '
                        'the full mixed scan using the existing layout contract. The continuous firing prefix '
                        'now enters the original P_BlockThingsIterator at 0x2c5a0 with the production path first '
                        'block coordinates in EAX/EDX, callback 0x2c720, return PC 0x2cab1 and retained line '
                        'intercepts; bound 383+281*list_length. No extra coordinate preservation premises. '
                        'Thing iterator body/bounds/list lookup, reachable input contracts, later cells, '
                        'clipping, damage and whole-tic parity remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: restored coordinates and continuous intended-cell thing CALL; strict axiom audit.')


if __name__ == '__main__':
    main()

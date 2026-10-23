#!/usr/bin/env python3
"""Certify option-word preservation and original thing-iterator CALL."""
import json
import re
import subprocess
import verify_e1m1_scan_return as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['flag_protected', 'caller_flag', 'call_collection', 'grid_stack', 'first_flag', 'flagged', 'flagged_finished', 'scan_flag', 'gate', 'called', 'enabled', 'firing_call']
NAMES = ['option_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingGate\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingGate
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1ThingGate
theorem option_checked (s : X86Memory.State) :
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4+(64#32))=
      load32 s.memory (s.regs 4+(64#32)) :=
  caller_flag s
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ThingGate.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedThingGate\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingGate.option_checked'"
    require(marker in output, 'missing thing-gate certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingGate.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1ThingGate.'+n for n in PROOFS]:
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
    out = ROOT/'artifacts/e1m1-thing-gate'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingGate'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Aim setup supplies option word 3. It survives the first complete line scan under '
                        'explicit stamp/array separation, so the original thing gate is enabled. '
                        'Continuous firing execution reaches P_BlockThingsIterator at 0x2c5a0 with callback '
                        '0x2c720, return PC 0x2cab1 and retained ordered line intercepts; bound '
                        '383+281*list_length. CALL arguments equal the actual ESI/ECX values at the gate. '
                        'Their correspondence to the intended cell, thing bounds/list lookup and traversal, '
                        'reachable input contracts, later cells, clipping, damage and whole-tic parity remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: derived thing flag, original CALL and retained intercepts; strict axiom audit.')


if __name__ == '__main__':
    main()

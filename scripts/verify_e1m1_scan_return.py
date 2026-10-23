#!/usr/bin/env python3
"""Certify saved-frame preservation and the first line-scan return to the thing gate."""
import json
import re
import subprocess
import verify_e1m1_firing_scan as previous
ROOT, require = previous.ROOT, previous.require
PROOFS = ['protect', 'protect_finished', 'stack_protected', 'prologue_words', 'caller_words', 'contains_dispatch', 'firing_frame', 'framed', 'finished', 'framed_finished', 'parent_return', 'firing_to_things']
NAMES = ['return_words_checked']
extracted = previous.extracted


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ScanReturn\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedScanReturn
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control E1M1ScanReturn
theorem return_words_checked (s : X86Memory.State) :
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4-(8#32))=s.regs 7 ∧
    load32 (E1M1PathMapCaller.scan s).core.memory (s.regs 4-(4#32))=(0x2ca94#32) :=
  caller_words s
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ScanReturn.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedScanReturn\n'


def audit(output):
    marker="'Doom.Verification.ExtractedScanReturn.return_words_checked'"
    require(marker in output, 'missing scan-return certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedScanReturn.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1ScanReturn.'+n for n in PROOFS]:
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
    out = ROOT/'artifacts/e1m1-scan-return'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ScanReturn'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='The original caller writes the saved EDI and actual return PC. A reusable preservation '
                        'extension protects both through the mixed scan without changing its execution. '
                        'Under firing-entry inputs and explicit heap/metadata separation, the first-cell '
                        'line scan returns true to 0x2ca94, restores SP and EDI, and executes the success '
                        'test to the thing gate at 0x2ca9c. Continuous prefix bound: 377+281*list_length. '
                        'Thing scanning is not executed by this theorem. Reachability, later cells, aim '
                        'clipping, damage, complete query/tic and audiovisual parity remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: saved frame, exact line return and caller success test; strict axiom audit.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Certify same-side rejection, early stop and finite traversal with all callback outcomes."""
import argparse
import json
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'entry_checked', 'firstShort_checked', 'secondWide_checked', 'secondShort_checked', 'secondReturn_checked', 'lineSide_checked', 'divlineSide_checked', 'execution_checked']
PROOFS = ['OriginalLineReject.tested_form', 'OriginalLineReject.saved_cursor', 'OriginalLineReject.tested_frame', 'OriginalLineReject.tested_observe', 'OriginalLineReject.callback_execution', 'OriginalLineReject.callback_continued', 'OriginalLineReject.entry_inputs', 'OriginalLineReject.execution', 'OriginalLineReject.continued', 'OriginalLineReject.frame', 'OriginalLineStop.zero', 'OriginalLineStop.finish_stack', 'OriginalLineStop.observed', 'OriginalLineStop.parent_return', 'OriginalLineTraversal.execution', 'OriginalLineTraversal.return_value', 'OriginalLineTraversal.stack', 'OriginalLineTraversal.of_mixed']

def certificate(raw):
    source = """import Doom.Proofs.OriginalLineTraversal
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineTraversal
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes'), ('entry', 'OriginalLineInterceptEntry.entryBytes'), ('firstShort', 'OriginalLineInterceptEntry.shortBytes'), ('secondWide', 'OriginalLineSecondPoint.wideBytes'), ('secondShort', 'OriginalLineSecondPoint.shortBytes'), ('secondReturn', 'OriginalLineSecondPoint.returnBytes'), ('lineSide', 'OriginalLineSide.code'), ('divlineSide', 'OriginalDivlineSide.code')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += """theorem execution_checked (s out : X86Control.State) (n : Nat)
    (h : OriginalLineTraversal.Runs s out n) :
    ∃ steps≤281*n+7, X86Routine.Prefix OriginalLineTraversal.program [] steps s out :=
  OriginalLineTraversal.execution s out n h
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineTraversal\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineTraversal.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-traversal.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-traversal'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.OriginalLineTraversal'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Finite original traversal includes sentinel, duplicate, same-side rejection, continuing crossings and early stop. Rejection restores and advances the cursor and returns no intercept; early stop restores protected parent-frame words. Per-reached-state contracts remain explicit; invariant closure and whole-game equivalence remain open.',
              'native_checks': 'No new native sampling: this batch composes previously checked instruction proofs. Kernel fixtures cover both side-test branches for same-side rejection followed by a duplicate and sentinel, and early stop without a suffix contract.'}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original rejection, early stop and traversal; extracted bytes and strict axiom audit.')



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise

#!/usr/bin/env python3
"""Certify callback-entry transport through both crossing tests and iterator resumption."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'entry_checked', 'firstShort_checked', 'secondWide_checked', 'secondShort_checked', 'secondReturn_checked', 'lineSide_checked', 'divlineSide_checked', 'execution_checked']
PROOFS = ['OriginalLineCrossing.tested_form', 'OriginalLineCrossing.tested_regs', 'OriginalLineCrossing.tested_frame', 'OriginalLineCrossing.fraction_inputs', 'OriginalLineCrossing.tail_inputs', 'OriginalLineCrossing.tail_protected', 'OriginalLineCrossing.frame', 'OriginalLineCrossing.saved_cursor', 'OriginalLineCrossing.return_side_safe', 'OriginalLineCrossing.saved_scratch_safe', 'OriginalLineCrossing.tail_layout', 'OriginalLineCrossing.tail_return', 'OriginalLineCrossing.contains_tests', 'OriginalLineCrossing.tests_execution', 'OriginalLineCrossing.ready', 'OriginalLineCrossing.execution', 'OriginalLineCrossing.continued', 'OriginalLineCrossing.live_append', 'E1M1LineCrossing.contains_cell', 'E1M1LineCrossing.callback_execution']

def certificate(raw):
    source = """import Doom.Proofs.E1M1LineCrossing
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineCrossing
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes'), ('entry', 'OriginalLineInterceptEntry.entryBytes'), ('firstShort', 'OriginalLineInterceptEntry.shortBytes'), ('secondWide', 'OriginalLineSecondPoint.wideBytes'), ('secondShort', 'OriginalLineSecondPoint.shortBytes'), ('secondReturn', 'OriginalLineSecondPoint.returnBytes'), ('lineSide', 'OriginalLineSide.code'), ('divlineSide', 'OriginalDivlineSide.code')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += """theorem execution_checked (s : X86Memory.State) (trace : Collision.Divline)
    (line : Collision.Line) (p v w : Word) (h : OriginalLineCrossing.Inputs s trace line p v w)
    (frac : Fixed) (flags : Nat) (data : OriginalLineCrossing.TailData s trace line frac flags p v)
    (f : Option Flags) :
    ∃ n≤270, X86Routine.Prefix OriginalLineCrossing.program [] n ⟨s,f,0x2c5f0⟩ (OriginalLineCrossing.result s) :=
  OriginalLineCrossing.execution s trace line p v w h frac flags data f
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineCrossing\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineCrossing.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-crossing.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-crossing'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.E1M1LineCrossing'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Crossing callback from 0x2c5f0 through both side tests, fraction helper, optional append and iterator resumption. Initial geometry, separation, successful arithmetic and capacity remain explicit. Mixed fresh/repeated loop and whole-game equivalence remain open.',
              'native_checks': 'No new native sampling: this batch composes previously checked instruction proofs. Kernel fixtures cover both side-test branches.'}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original crossing callback; extracted bytes and strict axiom audit.')



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise

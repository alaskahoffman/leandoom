#!/usr/bin/env python3
"""Certify fresh-line dispatch, stamp preservation and conditional mixed finite runs."""
import argparse
import json
import random
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'entry_checked', 'firstShort_checked', 'secondWide_checked', 'secondShort_checked', 'secondReturn_checked', 'lineSide_checked', 'divlineSide_checked', 'execution_checked']
PROOFS = ['OriginalLineDispatch.selected_regs', 'OriginalLineDispatch.entry_regs', 'OriginalLineDispatch.entry_frame', 'OriginalLineDispatch.entry_observe', 'OriginalLineDispatch.contains_cell', 'OriginalLineDispatch.entry_execution', 'OriginalLineDispatch.crossing_inputs', 'OriginalLineDispatch.record_safe', 'OriginalLineDispatch.tail_inputs', 'OriginalLineDispatch.execution', 'OriginalLineDispatch.continued', 'OriginalLineDispatch.callback_frame', 'OriginalLineDispatch.frame', 'OriginalLineDispatch.marked_seen', 'OriginalLineMixed.step_execution', 'OriginalLineMixed.execution', 'OriginalLineMixed.through_sentinel']

def certificate(raw):
    source = """import Doom.Proofs.OriginalLineMixed
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineDispatch
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes'), ('entry', 'OriginalLineInterceptEntry.entryBytes'), ('firstShort', 'OriginalLineInterceptEntry.shortBytes'), ('secondWide', 'OriginalLineSecondPoint.wideBytes'), ('secondShort', 'OriginalLineSecondPoint.shortBytes'), ('secondReturn', 'OriginalLineSecondPoint.returnBytes'), ('lineSide', 'OriginalLineSide.code'), ('divlineSide', 'OriginalDivlineSide.code')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += """theorem execution_checked (s : X86Memory.State) (trace : Collision.Divline)
    (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word)
    (h : OriginalLineDispatch.Ready s trace line frac flags p v w) (f : Option Flags) :
    ∃ n≤281, X86Routine.Prefix OriginalLineDispatch.program [] n ⟨s,f,0x2c57f⟩ (OriginalLineDispatch.result s) :=
  OriginalLineDispatch.execution s trace line frac flags p v w h f
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineDispatch\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineDispatch.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-dispatch.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-dispatch'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.OriginalLineMixed'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Fresh dispatch from list header, pre-stamp geometry transport, generated return word, stamp preservation, and conditional finite mixed crossing/duplicate iteration. Per-state fresh contracts remain explicit; rejection, early stop and a preserved whole-loop invariant remain open.',
              'native_checks': 'No new native sampling: this batch composes previously checked instruction proofs. Kernel fixtures cover both side-test branches and a fresh line-zero visit followed by its duplicate and sentinel.'}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original fresh dispatch and mixed loop; extracted bytes and strict axiom audit.')



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise

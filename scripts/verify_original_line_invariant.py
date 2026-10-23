#!/usr/bin/env python3
"""Certify rejection/duplicate scanning from an initial list-memory invariant."""
import argparse
import json
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'entry_checked', 'firstShort_checked', 'secondWide_checked', 'secondShort_checked', 'secondReturn_checked', 'lineSide_checked', 'divlineSide_checked', 'execution_checked']
PROOFS = ['OriginalLineInvariant.reject_inputs', 'OriginalLineInvariant.start', 'OriginalLineInvariant.item', 'OriginalLineInvariant.pointer', 'OriginalLineInvariant.view_stack', 'OriginalLineInvariant.protection', 'OriginalLineInvariant.ready', 'OriginalLineInvariant.advance', 'OriginalLineInvariant.walk', 'OriginalLineInvariant.through_sentinel', 'OriginalLineInvariant.frame', 'OriginalLineInvariant.parent_return']

def certificate(raw):
    source = """import Doom.Proofs.OriginalLineInvariant
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineInvariant
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes'), ('entry', 'OriginalLineInterceptEntry.entryBytes'), ('firstShort', 'OriginalLineInterceptEntry.shortBytes'), ('secondWide', 'OriginalLineSecondPoint.wideBytes'), ('secondShort', 'OriginalLineSecondPoint.shortBytes'), ('secondReturn', 'OriginalLineSecondPoint.returnBytes'), ('lineSide', 'OriginalLineSide.code'), ('divlineSide', 'OriginalDivlineSide.code')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += """theorem execution_checked (s : X86Memory.State) (n : Nat)
    (h : OriginalLineInvariant.Initial s n) (f : Option Flags) :
    ∃ steps≤178*n+7, X86Routine.Prefix OriginalLineInvariant.program [] steps
      ⟨s,f,0x2c57f⟩ (OriginalLineInvariant.finished n ⟨s,f,0x2c57f⟩) :=
  (OriginalLineInvariant.through_sentinel s n h f).1
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineInvariant\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineInvariant.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-invariant.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-invariant'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.OriginalLineInvariant'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Initial-memory invariant for finite lists whose fresh entries all reject geometrically. Current stamps select duplicate/rejection branches. Geometry, target and separation are transported to every reached state; the final sentinel comes from the initial image. Crossing/insertion and early-stop invariant closure, E1M1 map instantiation and whole-game equivalence remain open.',
              'native_checks': 'No new native sampling. Existing instruction proofs are composed; kernel fixtures exercise both geometry branches with a fresh rejection, its dynamically stamped duplicate, and sentinel return from one initial contract.'}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original initial-memory rejection/duplicate invariant; extracted bytes and strict axiom audit.')



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise

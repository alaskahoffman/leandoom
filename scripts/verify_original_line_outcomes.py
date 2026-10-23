#!/usr/bin/env python3
"""Certify all admitted line-callback outcomes from one initial-memory prefix."""
import argparse
import json
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'entry_checked', 'firstShort_checked', 'secondWide_checked', 'secondShort_checked', 'secondReturn_checked', 'lineSide_checked', 'divlineSide_checked', 'execution_checked']
PROOFS = ['OriginalLineNoInsert.disabled', 'OriginalLineNoInsert.frame', 'OriginalLineNoInsert.collection', 'OriginalLineNoInsert.negative_live', 'OriginalLineMixedInvariant.crossing_inputs', 'OriginalLineMixedInvariant.item', 'OriginalLineMixedInvariant.pointer', 'OriginalLineMixedInvariant.view_stack', 'OriginalLineMixedInvariant.dispatch_safe', 'OriginalLineMixedInvariant.side_safe', 'OriginalLineMixedInvariant.scratch_safe', 'OriginalLineMixedInvariant.protection', 'OriginalLineMixedInvariant.metadata', 'OriginalLineMixedInvariant.storage', 'OriginalLineMixedInvariant.record_safe', 'OriginalLineMixedInvariant.fresh', 'OriginalLineMixedInvariant.argument', 'OriginalLineMixedInvariant.geometry_read', 'OriginalLineMixedInvariant.reject_ready', 'OriginalLineMixedInvariant.crossing_ready', 'OriginalLineMixedInvariant.saved_cursor', 'OriginalLineMixedInvariant.advance', 'OriginalLineMixedInvariant.walk', 'OriginalLineMixedInvariant.start', 'OriginalLineMixedInvariant.through_sentinel', 'OriginalLineMixedInvariant.parent_return', 'OriginalLineScan.stopped_step', 'OriginalLineScan.scan_correct', 'OriginalLineScan.stopping_prefix', 'OriginalLineScan.through_scan', 'OriginalLineScan.stopped_parent']

def certificate(raw):
    source = """import Doom.Proofs.OriginalLineScan
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineScan
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes'), ('entry', 'OriginalLineInterceptEntry.entryBytes'), ('firstShort', 'OriginalLineInterceptEntry.shortBytes'), ('secondWide', 'OriginalLineSecondPoint.wideBytes'), ('secondShort', 'OriginalLineSecondPoint.shortBytes'), ('secondReturn', 'OriginalLineSecondPoint.returnBytes'), ('lineSide', 'OriginalLineSide.code'), ('divlineSide', 'OriginalDivlineSide.code')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += 'open OriginalLineMixedInvariant OriginalLineScan\ntheorem execution_checked (initial : X86Memory.State) (n : Nat) (base : Word)\n    (resolve : Collision.Intercept → Word)\n    (h : Initial initial n base resolve) (r : Collision.PathResult) (f : Option Flags)\n    (collected : OriginalLineCollection.Tracks initial base resolve r.collected n)\n    (sentinel : load16 initial.memory (address initial n)=(0xffff#16)) :\n    ∃ steps≤281*n+7, X86Routine.Prefix program [] steps ⟨initial,f,0x2c57f⟩\n      (complete h.candidates n ⟨initial,f,0x2c57f⟩ r).machine :=\n  (through_scan initial n base resolve h r f collected sentinel).2.1\n'
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineScan\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineScan.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-outcomes.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-outcomes'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.OriginalLineScan'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'All callback outcomes compose from one bounded initial prefix: duplicate, same-side rejection, negative fraction, append, and early stop. Stopping prefixes require no sentinel or suffix. Completed lists return through a separate initial sentinel premise. Ordered collection, cursor, protected memory and parent return are preserved. Concrete E1M1 query/map instantiation, overflow, and whole-game equivalence remain open.',
              'native_checks': 'No new native sampling. Kernel fixtures cover a nonempty collection, negative continuation with early-out enabled, and short/wide early stops with a non-sentinel next word. Previous append/duplicate/rejection fixtures remain checked.'}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original all-outcome line scan; extracted bytes and strict axiom audit.')



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise

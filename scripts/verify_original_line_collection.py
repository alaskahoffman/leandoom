#!/usr/bin/env python3
"""Certify ordered intercept collection, capacity reserves and original dispatch appends."""
import argparse
import json
import re
import subprocess
import verify_original_inline_thrust as extraction
ROOT, require = extraction.ROOT, extraction.require
NAMES = ['finish_checked', 'cell_checked', 'lineEntry_checked', 'lineReturn_checked', 'setup_checked', 'helper_checked', 'division_checked', 'entry_checked', 'firstShort_checked', 'secondWide_checked', 'secondShort_checked', 'secondReturn_checked', 'lineSide_checked', 'divlineSide_checked', 'execution_checked']
PROOFS = ['OriginalLineDispatchAppend.entry_encodes', 'OriginalLineDispatchAppend.live_append', 'OriginalLineCollection.slots_apart', 'OriginalLineCollection.capacity', 'OriginalLineCollection.old_record_safe', 'OriginalLineCollection.append', 'OriginalLineCollection.append_execution', 'OriginalLineCollection.preserve', 'OriginalLineCollection.duplicate', 'OriginalLineCollection.rejected']

def certificate(raw):
    source = """import Doom.Proofs.OriginalLineCollection
set_option maxRecDepth 32768
namespace Doom.Verification.ExtractedLineCollection
open Doom Doom.Proofs X86 X86Memory X86Control
"""
    for key,target in [('finish', 'OriginalLineFinish.code'), ('cell', 'OriginalLineCell.code'), ('lineEntry', 'OriginalLineBounds.lineEntry'), ('lineReturn', 'OriginalLineBounds.lineReturn'), ('setup', 'OriginalLineFraction.code'), ('helper', 'OriginalInterceptVector.code'), ('division', 'Doom19.fixedDivBytes'), ('entry', 'OriginalLineInterceptEntry.entryBytes'), ('firstShort', 'OriginalLineInterceptEntry.shortBytes'), ('secondWide', 'OriginalLineSecondPoint.wideBytes'), ('secondShort', 'OriginalLineSecondPoint.shortBytes'), ('secondReturn', 'OriginalLineSecondPoint.returnBytes'), ('lineSide', 'OriginalLineSide.code'), ('divlineSide', 'OriginalDivlineSide.code')]:
        source += 'def '+key+'Code : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+key+'_checked : '+key+'Code='+target+' := by decide\n'
    source += 'open OriginalLineCollection\ntheorem execution_checked (s : X86Memory.State) (f : Option Flags)\n    (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word)\n    (ready : OriginalLineDispatch.Ready s trace line frac flags p v w)\n    (r : Collision.PathResult) (id : Nat) (base : Word) (resolve : Collision.Intercept → Word) (reserve : Nat)\n    (tracked : Tracks s base resolve r.collected (reserve+1)) (layout : Layout s base)\n    (nonnegative : ¬frac.raw<0) (clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)\n    (pointer : resolve ⟨frac,true,id⟩=p)\n    (saved : OriginalLineTail.RecordSafe (OriginalLineDispatch.view s) ((OriginalLineDispatch.view s).regs 4-(12#32))) :\n    (∃ steps≤281, X86Routine.Prefix OriginalLineDispatch.program [] steps ⟨s,f,0x2c57f⟩ (OriginalLineDispatch.result s)) ∧\n    (OriginalLineDispatch.result s).pc=0x2c57f ∧\n    (OriginalLineDispatch.result s).core.regs 2=s.regs 2+(2#32) ∧\n    (OriginalLineDispatch.result s).core.regs 4=s.regs 4 ∧\n    Tracks (OriginalLineDispatch.result s).core base resolve (r.collected.push ⟨frac,true,id⟩) reserve :=\n  OriginalLineCollection.append_execution s f trace line frac flags p v w ready r id base resolve reserve tracked layout nonnegative clear pointer saved\n'
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedLineCollection\n'


def audit(output):
    rest = output.strip()
    for name in ['Doom.Verification.ExtractedLineCollection.' + n for n in NAMES] + ['Doom.Proofs.' + n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'") + r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: ' + name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected output')


def extracted():
    spec = json.loads((ROOT / 'tests/reference/original-line-collection.json').read_text())
    profile = json.loads((ROOT / 'tests/reference' / spec['exe_profile']).read_text())
    sw = json.loads((ROOT / 'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT / sw['local_directory'] / 'doom19s.zip', sw, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    spec, profile, raw = extracted()
    out = ROOT / 'artifacts/original-line-collection'
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'Extracted.lean'
    source.write_text(certificate(raw))
    subprocess.run([str(ROOT / 'scripts/lake'), 'build', 'Doom.Proofs.OriginalLineCollection'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT / 'scripts/lake'), 'env', 'lean', str(source)], cwd=ROOT, capture_output=True, text=True, check=True)
    audit(checked.stdout)
    (out / 'axioms.log').write_text(checked.stdout)
    report = {'exe_sha256': profile['exe_sha256'], 'units': spec['units'], 'axioms': checked.stdout.splitlines(),
              'scope': 'Ordered append correspondence from pre-dispatch memory, with capacity and old/new slot separation derived from a collection invariant. Duplicate and rejection visits preserve records while releasing a conservative reserve. Geometry/layout remain per-transition contracts; full mixed-loop invariant closure, map instantiation and whole-game equivalence remain open.',
              'native_checks': 'No new native sampling. Existing instruction proofs are composed; kernel fixtures append to a nonempty collection in both geometry branches, preserve the old record, advance the cursor, and preserve the collection through a dynamically marked duplicate.'}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: original ordered collection and dispatch append; extracted bytes and strict axiom audit.')



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '')
        print(error.stderr or '')
        raise

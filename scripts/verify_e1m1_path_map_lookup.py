#!/usr/bin/env python3
"""Bind every E1M1 cell's scan-entry contract to the original lookup bytes."""
import json
import re
import subprocess
import verify_e1m1_path_map as maps
import verify_original_inline_thrust as extraction
ROOT, require = maps.ROOT, maps.require
NAMES = ['bytes_checked', 'selected_checked', 'lookup_checked']
PROOFS = ['table_address', 'e1m1_index_bound', 'inputs_from_image', 'lookup_ready',
          'lookup_to_scan', 'lookup_preserves_collection']


def extracted():
    spec = json.loads((ROOT/'tests/reference/original-line-cell.json').read_text())
    profile = json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    return spec, profile, extraction.extract(binary, profile, spec)


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1PathMapLookup\n'+maps.certificate(data)
    source += '''namespace Doom.Verification.ExtractedPathMapLookup
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapLookup ExtractedPathMap
'''
    source += 'def bytes : List UInt8 := ['+','.join(hex(b) for b in raw['cell'])+']\n'
    source += '''theorem bytes_checked : bytes=OriginalLineCell.code := by decide +kernel

def cellFor (x y : Int32) (inside : Collision.pathCellInside x y 36 23=true) : Fin cells.size :=
  ⟨Collision.pathCellIndex x y 36,by rw [shape_checked.2.2.2]; exact e1m1_index_bound x y inside⟩

theorem selected_checked (x y : Int32) (inside : Collision.pathCellInside x y 36 23=true) :
    words[4+Collision.pathCellIndex x y 36]?=some cells[(cellFor x y inside).val].offset ∧
    cells[(cellFor x y inside).val].Valid words := cells_checked (cellFor x y inside)

/-- All in-bounds coordinates select their pinned cell directly. The actual
lookup supplies the cursor; no cell selection or post-lookup memory is assumed. -/
theorem lookup_checked (s : X86Memory.State) (f : Option Flags) (base lines : Word)
    (x y : Int32) (context : Context s base x y 36)
    (inside : Collision.pathCellInside x y 36 23=true)
    (image : WordImage s.memory base words) (lineBase : load32 s.memory 0x2c120=lines) :
    X86Routine.Prefix (OriginalLineCell.bytesProgram bytes) [] 8 ⟨s,f,0x2c541⟩ (OriginalLineCell.lookup s) ∧
    ScanWords (OriginalLineCell.lookup s).core lines cells[(cellFor x y inside).val] := by
  rw [bytes_checked]
  exact lookup_to_scan s f base lines words _ x y 36 23 context inside
    (selected_checked x y inside).2 image (selected_checked x y inside).1 lineBase
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMapLookup.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMapLookup\n'


def audit(output):
    marker="'Doom.Verification.ExtractedPathMapLookup.bytes_checked'"
    require(marker in output, 'missing lookup certificate audit')
    before, rest = output.split(marker, 1)
    maps.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathMapLookup.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMapLookup.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-path-map-lookup'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMapLookup'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='All in-bounds E1M1 coordinates select their certified cell. Eight extracted original '
                        'lookup instructions establish its scan cursor, ordered IDs, exact line pointers and '
                        'sentinel from the pre-lookup word image; lookup preserves all memory and collection capacity. '
                        'Loader image/global/register representation, bounds/grid-setup preservation, geometry, '
                        'visited stamps, later-cell capacity and complete-query equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original lookup establishes E1M1 scan-entry list facts for every in-bounds cell; strict axiom audit.')


if __name__ == '__main__':
    main()

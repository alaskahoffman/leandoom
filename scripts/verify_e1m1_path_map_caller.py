#!/usr/bin/env python3
"""Certify original grid caller through line bounds/lookup and outside return."""
import json
import re
import subprocess
import verify_e1m1_path_map_bounds as bounds
ROOT, require = bounds.ROOT, bounds.require
NAMES = ['dispatch_checked', 'inside_checked', 'outside_checked']
PROOFS = ['contains_dispatch', 'contains_bounds', 'call_stack', 'call_return', 'call_frame',
          'safe_at_call', 'bounds_inputs', 'globals_at_call', 'image_at_call', 'enter_execution',
          'inside_to_scan', 'outside_to_things', 'collection_preserved', 'contains_grid',
          'contains_caller', 'first_scan_execution']


def extracted():
    spec, profile, raw = bounds.extracted()
    cell = json.loads((ROOT/'tests/reference/original-path-cell.json').read_text())
    selected = dict(units={'dispatch': cell['units']['dispatch']})
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = bounds.lookup.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    raw.update(bounds.lookup.extraction.extract(binary, profile, selected, allowed_objects=(1,3)))
    return dict(units={**spec['units'], **selected['units']}), profile, raw


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1PathMapCaller\n'+bounds.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedPathMapCaller
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapLookup E1M1PathMapCaller ExtractedPathMap ExtractedPathMapLookup
'''
    source += 'def dispatchBytes : List UInt8 := ['+','.join(hex(b) for b in raw['dispatch'])+']\n'
    source += '''theorem dispatch_checked : dispatchBytes=OriginalPathCell.code := by decide +kernel

theorem inside_checked (s : X86Memory.State) (f : Option Flags) (base lines : Word) (x y : Int32)
    (enabled : OriginalPathCell.enabled true s=true) (dims : Dimensions s 36 23)
    (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec) (globals : Globals s base lines)
    (inside : Collision.pathCellInside x y 36 23=true)
    (image : WordImage s.memory base words) (safe : ImageSafe s base words) :
    (∃ n≤30, X86Routine.Prefix (bytesProgram dispatchBytes ExtractedPathMapBounds.entryBytes
      ExtractedPathMapBounds.returnBytes bytes) [] n ⟨s,f,0x2ca7f⟩ (scan s)) ∧
    ScanWords (scan s).core lines cells[(cellFor x y inside).val] ∧
    (scan s).pc=0x2c57f ∧ (scan s).core.regs 4=s.regs 4-(12#32) := by
  rw [dispatch_checked,ExtractedPathMapBounds.entry_checked,ExtractedPathMapBounds.return_checked,bytes_checked]
  exact inside_to_scan s f base lines words _ x y 36 23 enabled dims mapX mapY globals inside
    (selected_checked x y inside).2 image safe (selected_checked x y inside).1

theorem outside_checked (s : X86Memory.State) (f : Option Flags) (x y : Int32)
    (enabled : OriginalPathCell.enabled true s=true) (dims : Dimensions s 36 23)
    (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec)
    (outside : Collision.pathCellInside x y 36 23=false) :
    (∃ n≤24, X86Routine.Prefix (bytesProgram dispatchBytes ExtractedPathMapBounds.entryBytes
      ExtractedPathMapBounds.returnBytes bytes) [] n ⟨s,f,0x2ca7f⟩ (resumed s)) ∧
    (resumed s).pc=0x2ca9c ∧ (resumed s).core.regs 4=s.regs 4 ∧ (resumed s).core.regs 0=1 := by
  rw [dispatch_checked,ExtractedPathMapBounds.entry_checked,ExtractedPathMapBounds.return_checked,bytes_checked]
  exact outside_to_things s f x y 36 23 enabled dims mapX mapY outside
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMapCaller.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMapCaller\n'


def audit(output):
    marker="'Doom.Verification.ExtractedPathMapCaller.dispatch_checked'"
    require(marker in output, 'missing caller certificate audit')
    before, rest = output.split(marker, 1)
    bounds.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathMapCaller.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMapCaller.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-path-map-caller'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMapCaller'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='The enabled original grid caller reaches scan entry within 30 instructions, '
                        'or returns from an outside cell through the caller success test within 24. '
                        'Pre-call separation protects map words, globals and existing records across CALL and both '
                        'prologue stores. The existing pistol/shotgun firing prefix joins to scan entry, deriving '
                        'coordinates and enable flags. Map image/globals/separation remain premises at the first '
                        'grid state; earlier image preservation, loader connection, geometry, visited stamps, '
                        'later-cell capacity and complete-query equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: pinned grid caller to scan, outside return to things gate, collection frame and shared firing join; strict axiom audit.')


if __name__ == '__main__':
    main()

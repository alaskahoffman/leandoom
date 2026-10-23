#!/usr/bin/env python3
"""Certify original bounds-to-scan execution and outside-cell return."""
import json
import re
import subprocess
import verify_e1m1_path_map_lookup as lookup
ROOT, require = lookup.ROOT, lookup.require
NAMES = ['entry_checked', 'return_checked', 'inside_checked', 'outside_checked']
PROOFS = ['contains_bounds', 'contains_lookup', 'result_memory', 'result_frame',
          'image_preserved', 'lookup_context', 'inside_to_scan', 'outside_returns', 'collection_preserved']


def extracted():
    spec, profile, raw = lookup.extracted()
    bounds = json.loads((ROOT/'tests/reference/original-path-cell.json').read_text())
    selected = dict(units={k: bounds['units'][k] for k in ['lineEntry', 'lineReturn']})
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = lookup.extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    raw.update(lookup.extraction.extract(binary, profile, selected))
    return dict(units={**spec['units'], **selected['units']}), profile, raw


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1PathMapBounds\n'+lookup.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedPathMapBounds
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapLookup E1M1PathMapBounds ExtractedPathMap ExtractedPathMapLookup
'''
    for key, name, target in [('lineEntry', 'entry', 'lineEntry'), ('lineReturn', 'return', 'lineReturn')]:
        source += 'def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[key])+']\n'
        source += 'theorem '+name+'_checked : '+name+'Bytes=OriginalLineBounds.'+target+' := by decide +kernel\n'
    source += '''
theorem inside_checked (s : X86Memory.State) (f : Option Flags) (base lines : Word) (x y : Int32)
    (bounds : OriginalLineBounds.Inputs s x y 36 23) (globals : Globals s base lines)
    (inside : Collision.pathCellInside x y 36 23=true)
    (image : WordImage s.memory base words) (safe : ImageSafe s base words) :
    (∃ n≤24, X86Routine.Prefix (E1M1PathMapBounds.bytesProgram entryBytes returnBytes bytes) [] n
      ⟨s,f,0x2c520⟩ (scanStart s)) ∧
    ScanWords (scanStart s).core lines cells[(cellFor x y inside).val] ∧
    (scanStart s).pc=0x2c57f ∧ (scanStart s).core.regs 4=s.regs 4-(8#32) := by
  rw [entry_checked,return_checked,bytes_checked]
  exact inside_to_scan s f base lines words _ x y 36 23 bounds globals inside
    (selected_checked x y inside).2 image safe (selected_checked x y inside).1

theorem outside_checked (s : X86Memory.State) (f : Option Flags) (x y : Int32)
    (bounds : OriginalLineBounds.Inputs s x y 36 23) (outside : Collision.pathCellInside x y 36 23=false) :
    (∃ n≤16, X86Routine.Prefix (E1M1PathMapBounds.bytesProgram entryBytes returnBytes bytes) [] n
      ⟨s,f,0x2c520⟩ (OriginalLineBounds.result s)) ∧
    (OriginalLineBounds.result s).core.regs 0=1 ∧
    (OriginalLineBounds.result s).core.regs 4=s.regs 4+4 ∧
    (OriginalLineBounds.result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  rw [entry_checked,return_checked,bytes_checked]
  exact outside_returns s f x y 36 23 bounds outside
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMapBounds.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMapBounds\n'


def audit(output):
    marker="'Doom.Verification.ExtractedPathMapBounds.entry_checked'"
    require(marker in output, 'missing bounds certificate audit')
    before, rest = output.split(marker, 1)
    lookup.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathMapBounds.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMapBounds.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-path-map-bounds'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMapBounds'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Inside cells reach the scan header through original prologue, signed bounds and lookup '
                        'within 24 instructions; outside cells return true within 16 without a map-image premise. '
                        'Pre-entry separation protects map words, globals and existing intercept records from '
                        'both stack writes. Loader image, upstream grid caller, geometry, visited stamps, '
                        'later-cell capacity and complete-query equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: pinned original bounds-to-scan join, protected map/collection and outside-cell return; strict axiom audit.')


if __name__ == '__main__':
    main()

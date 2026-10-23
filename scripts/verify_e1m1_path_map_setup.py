#!/usr/bin/env python3
"""Certify map and initial collection transport from traversal entry to scan."""
import json
import re
import subprocess
import verify_e1m1_path_map_caller as caller
ROOT, require = caller.ROOT, caller.require
SEGMENTS = {'init': 'OriginalPathInit.code', 'xstep': 'OriginalPathXStep.code',
            'abs': 'OriginalAbs.code', 'division': 'Doom19.fixedDivBytes',
            'intercept': 'OriginalPathIntercept.code', 'ystep': 'OriginalPathYStep.code',
            'second': 'OriginalPathSecondIntercept.code'}
NAMES = [name+'_checked' for name in SEGMENTS]+['map_checked', 'collection_checked']
PROOFS = ['x_safe', 'y_safe', 'after_stack', 'after_frame', 'grid_stack', 'grid_frame',
          'caller_safe', 'map_at_grid', 'initial_collection_at_scan', 'first_scan_execution']


def extracted():
    spec, profile, raw = caller.extracted()
    units = dict(spec['units'])
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    extraction = caller.bounds.lookup.extraction
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    for name in ['init', 'xstep', 'intercept', 'ystep']:
        part = json.loads((ROOT/f'tests/reference/original-path-{name}.json').read_text())
        for key, value in part['units'].items():
            if key in units:
                require(units[key] == value, 'conflicting segment: '+key)
            units[key] = value
        raw.update(extraction.extract(binary, profile, part, allowed_objects=(1,3)))
    require(set(SEGMENTS) <= set(raw), 'missing setup segment')
    return dict(units=units), profile, raw


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1PathMapSetup\n'+caller.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedPathMapSetup
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapSetup ExtractedPathMap
'''
    for name, target in SEGMENTS.items():
        source += 'def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source += 'theorem '+name+'_checked : '+name+'Bytes='+target+' := by decide +kernel\n'
    source += '''
theorem map_checked (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (base lines : Word)
    (map : MapInputs s base lines words 36 23) :
    E1M1PathMapCaller.Dimensions (grid s).core 36 23 ∧
    E1M1PathMapCaller.Globals (grid s).core base lines ∧
    WordImage (grid s).core.memory base words ∧ E1M1PathMapCaller.ImageSafe (grid s).core base words :=
  map_at_grid s ox oy sx sy ex ey geometry base lines words 36 23 map

theorem collection_checked (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (i : Fin cells.size)
    (resolver : Collision.Intercept → Word)
    (cursorSafe : StackSafe (s.regs 4-(60#32)) (0x2c028#32)) :
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (grid s).core).core 0x2ba20 resolver #[] cells[i.val].ids.length :=
  initial_collection_at_scan s ox oy sx sy ex ey geometry words cells[i.val]
    (cells_checked i).2 resolver cursorSafe
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMapSetup.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMapSetup\n'


def audit(output):
    marker="'Doom.Verification.ExtractedPathMapSetup.init_checked'"
    require(marker in output, 'missing setup certificate audit')
    before, rest = output.split(marker, 1)
    caller.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathMapSetup.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMapSetup.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-path-map-setup'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMapSetup'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Map contents, dimensions, globals and separation are transported from traversal entry '
                        'through initialization and both axis/intercept setups into the caller-to-scan proof. '
                        'The initialized empty intercept cursor and per-cell reserve are derived at scan entry. '
                        'The shared pistol/shotgun firing join needs no first-grid map or empty-collection premise. '
                        'Loader linkage and preservation before traversal entry, line geometry/visited state, '
                        'callback storage, later-cell capacity and complete-query equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: traversal-entry map transport, initialized collection at scan, shared firing join; pinned bytes and strict axiom audit.')


if __name__ == '__main__':
    main()

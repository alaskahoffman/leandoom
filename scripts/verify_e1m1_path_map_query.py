#!/usr/bin/env python3
"""Certify protected map transport through aim ray and traversal setup."""
import json
import re
import subprocess
import verify_e1m1_path_map_setup as setup
ROOT, require = setup.ROOT, setup.require
SEGMENTS = {'ray': 'OriginalAimQuery.rayBytes', 'setup': 'OriginalAimSetup.code'}
NAMES = [name+'_checked' for name in SEGMENTS]+['map_checked', 'execution_checked']
PROOFS = ['ray_stack', 'traversal_stack', 'setup_safe', 'traversal_safe', 'traversal_frame',
          'map_at_traversal', 'cursor_at_traversal', 'origins_at_traversal', 'query_execution', 'first_scan_execution']


def extracted():
    spec, profile, raw = setup.extracted()
    units = dict(spec['units'])
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    extraction = setup.caller.bounds.lookup.extraction
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    for name in ['query', 'setup']:
        part = json.loads((ROOT/f'tests/reference/original-aim-{name}.json').read_text())
        part['units'] = {key: value for key, value in part['units'].items() if key in SEGMENTS}
        for key, value in part['units'].items():
            if key in units:
                require(units[key] == value, 'conflicting segment: '+key)
            units[key] = value
        raw.update(extraction.extract(binary, profile, part, allowed_objects=(1,3)))
    require(set(SEGMENTS) <= set(raw), 'missing setup segment')
    return dict(units=units), profile, raw


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1PathMapQuery\n'+setup.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedPathMapQuery
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapQuery ExtractedPathMap
'''
    for name, target in SEGMENTS.items():
        source += 'def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source += 'theorem '+name+'_checked : '+name+'Bytes='+target+' := by decide +kernel\n'
    source += '''
theorem map_checked (s : X86Memory.State) (base lines : Word)
    (map : MapInputs s base lines words 36 23) :
    E1M1PathMapSetup.MapInputs (traversal s).core base lines words 36 23 :=
  map_at_traversal s base lines words 36 23 map

theorem execution_checked (s : X86Memory.State) (f : Option Flags) (base lines : Word)
    (map : MapInputs s base lines words 36 23) :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimSetup.program [] 36 ⟨s,f,0x2bb80⟩ (traversal s) ∧
    E1M1PathMapSetup.MapInputs (traversal s).core base lines words 36 23 :=
  query_execution s f base lines words 36 23 map
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMapQuery.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMapQuery\n'


def audit(output):
    marker="'Doom.Verification.ExtractedPathMapQuery.ray_checked'"
    require(marker in output, 'missing setup certificate audit')
    before, rest = output.split(marker, 1)
    setup.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathMapQuery.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMapQuery.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = setup.caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-path-map-query'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMapQuery'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Protected map words and globals now survive the 36-instruction aim-query prologue, '
                        'ray arithmetic and setup through the traversal CALL. Traversal/scan stack protection '
                        'and cursor safety are derived from the query-entry layout. The shared firing join '
                        'uses the map contract at first query entry, with no later map-image assumption. '
                        'Earlier firing preservation, loader linkage, shooter/table geometry encodings, '
                        'visited state, callback storage, later-cell capacity and complete-query equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: query-entry map transport, protected origins/cursor layout and shared scan join; pinned bytes and strict axiom audit.')


if __name__ == '__main__':
    main()

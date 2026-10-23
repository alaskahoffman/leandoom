#!/usr/bin/env python3
"""Certify protected map transport through firing setters and bullet-slope setup."""
import json
import re
import subprocess
import verify_e1m1_path_map_query as setup
ROOT, require = setup.ROOT, setup.require
SEGMENTS = {'pistol': 'OriginalWeaponDischarge.pistolBytes',
            'shotgun': 'OriginalWeaponDischarge.shotgunBytes',
            'actor': 'Doom19.setMobjStateBytes', 'flash': 'PspriteSetter.code',
            'light': 'PspriteLight.code 1', 'slope': 'OriginalBulletSlope.code'}
NAMES = [name+'_checked' for name in SEGMENTS]+['map_checked', 'execution_checked']
PROOFS = ['slope_stack', 'slope_frame', 'flashed_stack', 'aim_stack', 'query_stack',
          'query_frame', 'query_safe', 'map_at_query', 'cursor_at_query', 'query_execution', 'first_scan_execution']


def extracted():
    spec, profile, raw = setup.extracted()
    units = dict(spec['units'])
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    extraction = setup.setup.caller.bounds.lookup.extraction
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip', share, profile)
    for path in ['e1m1-discharge-setters', 'original-bullet-slope']:
        part = json.loads((ROOT/f'tests/reference/{path}.json').read_text())
        for key, value in part['units'].items():
            if key in units:
                require(units[key] == value, 'conflicting segment: '+key)
            units[key] = value
        raw.update(extraction.extract(binary, profile, part, allowed_objects=(1,3)))
    require(set(SEGMENTS) <= set(raw), 'missing setup segment')
    return dict(units=units), profile, raw


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1PathMapFiring\n'+setup.certificate(data, raw)
    source += '''namespace Doom.Verification.ExtractedPathMapFiring
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1PathMap E1M1PathMapFiring ExtractedPathMap
'''
    for name, target in SEGMENTS.items():
        source += 'def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source += 'theorem '+name+'_checked : '+name+'Bytes='+target+' := by decide +kernel\n'
    source += '''
theorem map_checked (gun : Fire.Gun) (s : X86Memory.State) (base lines : Word)
    (map : MapInputs gun s base lines words 36 23) :
    E1M1PathMapQuery.MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words 36 23 :=
  map_at_query gun s base lines words 36 23 map

theorem execution_checked (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (base lines : Word) (map : MapInputs gun s base lines words 36 23) :
    (∃ n≤127, X86CodeMemory.Prefix FloorCaller.cm E1M1BulletAim.program [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (E1M1BulletAim.firstQuery gun s)) ∧
    E1M1PathMapQuery.MapInputs (E1M1BulletAim.firstQuery gun s).core base lines words 36 23 :=
  query_execution gun s f weapon input base lines words 36 23 map
'''
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1PathMapFiring.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedPathMapFiring\n'


def audit(output):
    marker="'Doom.Verification.ExtractedPathMapFiring.pistol_checked'"
    require(marker in output, 'missing setup certificate audit')
    before, rest = output.split(marker, 1)
    setup.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedPathMapFiring.'+n for n in NAMES]+[
            'Doom.Proofs.E1M1PathMapFiring.'+n for n in PROOFS]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = setup.setup.caller.bounds.lookup.maps.pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-path-map-firing'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1PathMapFiring'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Post-sound map image and globals survive pose, debit, flash/light, aim CALL and '
                        'bullet-slope saves through first query entry. Both weapons share the <=368-instruction '
                        'first-scan join with no intermediate map-image assumption. Loader linkage, earlier '
                        'sound preservation, shooter/table geometry, visited state, callback storage, '
                        'later-cell capacity and complete-query equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: post-sound map transport and shared firing-to-scan join; pinned bytes and strict axiom audit.')


if __name__ == '__main__':
    main()

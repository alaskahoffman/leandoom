#!/usr/bin/env python3
"""Certify continuous firing-entry execution through first-cell object traversal."""
import json
import re
import subprocess
import verify_e1m1_thing_traversal as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1ScanCapacity': ['step_size', 'run_size', 'finished_size'], 'E1M1ThingListInputs': ['capacity', 'all_lines', 'entry_read', 'trace_read', 'trace_words', 'geometry', 'linked', 'static_layout'], 'E1M1FiringThings': ['contains_entry', 'saved_words', 'image', 'layout', 'execution', 'scene_cell', 'execution_scene']}


def extracted():
    return previous.extracted()


def pinned_data():
    return previous.pinned_data()


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringThings\n'+previous.certificate(data, raw)
    for module, names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1ScanCapacity.step_size'"
    require(marker in output, 'missing firing-things certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Proofs.'+module+'.'+n for module,names in GROUPS.items() for n in names]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    data, map_profile = pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-firing-things'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1FiringThings'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Uses the existing 28 authenticated DOS ranges. Initial firing-state actor '
                        'fields and links are transported through setup and the line scan; trace words '
                        'come from actual path initialization. The original CALL/prologue writes derive '
                        'the callback and caller words. A conservative candidate-count capacity bound '
                        'supplies space for the complete line and object lists. A continuous prefix '
                        'from either gun common post-sound entry reaches the first-cell object-iterator '
                        'return site 0x2cab1 within 406+281*line_count+230*object_count instructions, '
                        'including empty lists. The mixed collection matches the selected production '
                        'scene cell lookup/intersection/append fragment in order. No reached-state image '
                        'or callback result is assumed. Initial encodings, static separation, arithmetic '
                        'success, finite-list and scene relations, and the candidate-count bound still '
                        'require reachable-state discharge. Caller register invariants and success test, '
                        'outer grid walk/later cells, clipping, damage, full query/tic and audiovisual '
                        'correspondence remain open. No runtime changes or independent emulator '
                        'crosscheck are claimed.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: firing-entry first-cell object traversal; strict axiom audit.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Certify saved grid coordinates and firing-entry return through the caller success test."""
import json
import re
import subprocess
import verify_e1m1_firing_things as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1ThingPreservation': ['slot_address', 'saved_prologue', 'entry_saved', 'finish_coordinate', 'resume_coordinate', 'visit_coordinate', 'run_coordinate', 'return_coordinate', 'traversal_coordinate', 'lookup_coordinate'], 'E1M1FiringCellReturn': ['contains_cell', 'success_test', 'boundary_coordinate', 'firing_coordinate', 'execution']}


def extracted():
    return previous.extracted()


def pinned_data():
    return previous.pinned_data()


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringCellReturn\n'+previous.certificate(data, raw)
    for module, names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1ThingPreservation.slot_address'"
    require(marker in output, 'missing firing-cell-return certificate audit')
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
    out = ROOT/'artifacts/e1m1-firing-cell-return'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1FiringCellReturn'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Uses the existing 28 authenticated DOS ranges. Both ECX/ESI grid coordinates '
                        'are restored from actual callback stack saves through rejection/insertion, '
                        'all finite list nodes, iterator setup/lookup and epilogue. Existing stack '
                        'separation suffices; no new reached-coordinate or per-visit outcome premise. '
                        'A continuous prefix from either post-sound weapon entry executes the caller '
                        'TEST/JZ and reaches 0x2cab5 in at most 408+281*line_count+230*object_count '
                        'modeled instructions, retaining the selected first cell coordinates and '
                        'ordered mixed intercept collection. Empty/nonempty lists are covered. '
                        'Initial encodings, finite-list/scene relation, arithmetic success, separation '
                        'and conservative capacity remain conditional. Grid-step execution, other '
                        'caller registers/locals needed for stepping, later cells, clipping/damage, '
                        'full query/tic and audiovisual correspondence remain open. No runtime '
                        'changes or independent emulator crosscheck are claimed.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: firing-entry first-cell coordinates and caller success; strict axiom audit.')


if __name__ == '__main__':
    main()

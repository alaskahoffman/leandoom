#!/usr/bin/env python3
"""Certify finite DOS object-list traversal, production collection, and return."""
import json
import re
import subprocess
import verify_e1m1_thing_finish as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1ThingVisit': ['contains_first', 'contains_second', 'contains_callback', 'contains_iterator', 'entry_inputs', 'body', 'body_collection', 'execution', 'frame'], 'E1M1ThingList': ['layout_tail', 'geometry_transport', 'linked_transport', 'collect_size', 'visit_inputs', 'image_tail', 'execution'], 'E1M1ThingTraversal': ['return_observe', 'execution', 'collect_fold', 'objectCell_collect', 'execution_cell']}


def extracted():
    return previous.extracted()


def pinned_data():
    return previous.pinned_data()


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingTraversal\n'+previous.certificate(data, raw)
    for module, names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1ThingVisit.contains_first'"
    require(marker in output, 'missing thing-traversal certificate audit')
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
    out = ROOT/'artifacts/e1m1-thing-traversal'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingTraversal'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Reuses the 28 authenticated DOS ranges. A generic complete object visit '
                        'is proved from raw geometry, memory and arithmetic contracts. A finite-list '
                        'induction preserves trace/object encodings, links, callback and caller words '
                        'through all visits. From the list-head/empty-list seam, the list and real '
                        'iterator epilogue execute within 230*node_count+3 instructions and return '
                        'success to the saved caller, with the ordered intercept collection matching '
                        'a loop using the production scene lookup, thingIntercept and appendIntercept. '
                        'Capacity reserves one slot per node, including rejected nodes. Static list '
                        'layout, initial image, finite node order, scene lookup and arithmetic success '
                        'remain explicit contracts. Transport of this whole-list contract from the '
                        'firing entry, outer cell traversal, reachable-state discharge, damage and '
                        'whole-tic/observable equivalence remain open. No new DOS code ranges or '
                        'independent emulator crosscheck were added.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: finite original object-list traversal and iterator return; strict axiom audit.')


if __name__ == '__main__':
    main()

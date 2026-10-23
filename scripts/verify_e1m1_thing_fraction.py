#!/usr/bin/env python3
"""Certify the DOS object fraction and its rejection/insertion branch from firing entry."""
import json
import re
import subprocess
import verify_e1m1_thing_crossing as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalThingFraction': ['decoded', 'contains_helper', 'setup_execution', 'fraction_execution', 'setup_regs', 'setup_return', 'returned', 'setup_memory', 'local_frame', 'local_x', 'local_y', 'local_dx', 'local_dy', 'encoded', 'live', 'test_execution', 'execution', 'decision_live', 'production', 'setup_frame', 'frame'], 'OriginalThingFractionInputs': ['second_regs', 'crossing_regs', 'endpoints', 'inputs'], 'E1M1ThingFraction': ['contains_prior', 'contains_fraction', 'continue_live', 'collection', 'firing_fraction']}
SEGMENTS = ["thingFraction"]
NAMES = ["thingFraction_checked","execution_checked"]


def extracted():
    import verify_original_inline_thrust as extraction
    spec, profile, raw = previous.extracted()
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    part = json.loads((ROOT/'tests/reference/original-thing-fraction.json').read_text())
    require(part['exe_profile']=='original-mul.json','unexpected executable profile')
    extra = extraction.extract(binary,profile,part)
    require(not(set(spec['units']) & set(extra)),'conflicting thing code range')
    return dict(units={**spec['units'],**part['units']}),profile,{**raw,**extra}


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingFraction\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingFraction
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
"""
    for name in SEGMENTS:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Bytes=OriginalThingFraction.'+name+' := by decide\n'
    source+="""theorem execution_checked (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalInterceptVector.Safe (OriginalThingFraction.setup s)) :
    ∃ n≤80, X86Routine.Prefix (OriginalThingFraction.bytesProgram thingFractionBytes)
      [] n ⟨s,f,0x2c7ae⟩ (OriginalThingFraction.result s) := by
  rw [thingFraction_checked]
  exact OriginalThingFraction.execution s f safe
"""
    source+='\n'.join('#print axioms '+n for n in NAMES)+'\n'
    for module,names in GROUPS.items():
        source+='\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source+'end Doom.Verification.ExtractedThingFraction\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingFraction.thingFraction_checked'"
    require(marker in output, 'missing thing-fraction certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingFraction.'+n for n in NAMES]+[
            'Doom.Proofs.'+module+'.'+n for module,names in GROUPS.items() for n in names]:
        match = re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def pinned_data():
    return previous.pinned_data()


def main():
    data, map_profile = pinned_data()
    spec, profile, raw = extracted()
    require(profile['exe_sha256'] == map_profile['exe_sha256'], 'executable profile mismatch')
    out = ROOT/'artifacts/e1m1-thing-fraction'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingFraction'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='One additional authenticated DOS range constructs the object diagonal on the '
                        'stack, calls the proved intersection helper, and selects negative-fraction rejection '
                        'or object insertion. Endpoint and trace facts are transported through both side '
                        'tests from the callback entry. The firing-level join derives those facts from '
                        'common post-sound entry and reaches a rejection/insertion boundary within '
                        '613+281*list_length instructions, preserving existing line intercepts. The '
                        'production thingIntercept returns exactly the corresponding optional fraction. '
                        'Initial representation/separation and successful production arithmetic on crossings '
                        'remain hypotheses. Object record writes, callback epilogue/list traversal, later '
                        'cells, reachable-state discharge, damage, and whole-tic/observable equivalence '
                        'remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original object fraction and firing-entry rejection/insertion branch; strict axiom audit.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Certify the original thing iterator bounds, first pointer lookup and firing join."""
import json
import re
import subprocess
import verify_e1m1_thing_coordinates as previous
ROOT, require = previous.ROOT, previous.require
GENERIC = ['decoded', 'entry_execution', 'guard_execution', 'return_execution', 'guarded_pc', 'lookup_execution', 'lookup_finish_execution', 'execution', 'entry_frame', 'guard_frame', 'entry_coordinates', 'live_bounds', 'inside_state', 'result_memory', 'frame', 'return_word', 'outside_return', 'live_head', 'nonempty', 'empty_return']
PROOFS = ['contains_prior', 'contains_thing', 'collection', 'extended', 'scan_read', 'result', 'call_read', 'call_stack', 'firing_execution', 'reads', 'bounds_inputs', 'first_head', 'firing_lookup']
SEGMENTS = ['thingEntry','thingLookup','thingReturn']
NAMES = [n+'_checked' for n in SEGMENTS]+['execution_checked']


def extracted():
    import verify_original_inline_thrust as extraction
    spec, profile, raw = previous.extracted()
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    part = json.loads((ROOT/'tests/reference/original-thing-entry.json').read_text())
    require(part['exe_profile']=='original-mul.json','unexpected executable profile')
    extra = extraction.extract(binary,profile,part)
    require(not(set(spec['units']) & set(extra)),'conflicting thing code range')
    return dict(units={**spec['units'],**part['units']}),profile,{**raw,**extra}


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingEntry\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingEntry
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
"""
    for name in SEGMENTS:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Bytes=OriginalThingEntry.'+name+' := by decide\n'
    source+="""theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤20, X86Routine.Prefix (OriginalThingEntry.bytesProgram thingEntryBytes thingLookupBytes thingReturnBytes)
      [] n ⟨s,f,0x2c5a0⟩ (OriginalThingEntry.result s) := by
  rw [thingEntry_checked,thingLookup_checked,thingReturn_checked]
  exact OriginalThingEntry.execution s f
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.OriginalThingEntry.'+n for n in GENERIC)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ThingEntry.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedThingEntry\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingEntry.thingEntry_checked'"
    require(marker in output, 'missing thing-entry certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingEntry.'+n for n in NAMES]+[
            'Doom.Proofs.OriginalThingEntry.'+n for n in GENERIC]+[
            'Doom.Proofs.E1M1ThingEntry.'+n for n in PROOFS]:
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
    out = ROOT/'artifacts/e1m1-thing-entry'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingEntry'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Three new pinned DOS code ranges cover the thing iterator prologue, signed bounds, '
                        'first object-pointer lookup and successful return. From explicit common post-sound '
                        'firing memory/separation contracts, continuous execution reaches the selected first '
                        'object at 0x2c5d2 or returns true to 0x2cab1 for an empty cell, preserving collected '
                        'line intercepts; bound 403+281*list_length. Table/global reads are transported from '
                        'firing entry, not assumed at the reached iterator. The object callback/list traversal, '
                        'reachable-state discharge of input contracts, later cells, clipping, damage and '
                        'whole-tic correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original thing bounds, first pointer lookup and continuous firing join; strict axiom audit.')


if __name__ == '__main__':
    main()

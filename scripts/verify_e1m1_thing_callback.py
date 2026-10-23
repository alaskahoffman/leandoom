#!/usr/bin/env python3
"""Certify the original object callback handoff, prologue, and return-side list decision."""
import json
import re
import subprocess
import verify_e1m1_thing_entry as previous
ROOT, require = previous.ROOT, previous.require
GENERIC = ['decoded', 'call_execution', 'call_observe', 'call_frame', 'prepare_execution', 'prepare_observe', 'prepare_frame', 'slots_apart', 'saved_cursor', 'saved_return', 'resume_execution', 'resumed_observe', 'enter_execution', 'enter_observe', 'enter_frame']
PROOFS = ['contains_prior', 'contains_callback', 'collection', 'firing_enter']
SEGMENTS = ['thingCall','thingPrepare']
NAMES = [n+'_checked' for n in SEGMENTS]+['execution_checked','resume_checked']


def extracted():
    import verify_original_inline_thrust as extraction
    spec, profile, raw = previous.extracted()
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    part = json.loads((ROOT/'tests/reference/original-thing-callback.json').read_text())
    require(part['exe_profile']=='original-mul.json','unexpected executable profile')
    extra = extraction.extract(binary,profile,part)
    require(not(set(spec['units']) & set(extra)),'conflicting thing code range')
    return dict(units={**spec['units'],**part['units']}),profile,{**raw,**extra}


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingCallback\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingCallback
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
"""
    for name in SEGMENTS:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Bytes=OriginalThingCallback.'+name+' := by decide\n'
    source+="""theorem execution_checked (s : X86Memory.State) (f : Option Flags)
    (target : load32 s.memory (s.regs 4)=(0x2c720#32)) :
    X86Routine.Prefix (OriginalThingCallback.bytesProgram thingCallBytes thingPrepareBytes)
      [] 10 ⟨s,f,0x2c5d2⟩ (OriginalThingCallback.entered s f) := by
  rw [thingCall_checked,thingPrepare_checked]
  exact OriginalThingCallback.enter_execution s f target
 theorem resume_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤5, X86Routine.Prefix (OriginalThingCallback.bytesProgram thingCallBytes thingPrepareBytes)
      [] n ⟨s,f,0x2c5d7⟩ (OriginalThingCallback.resumed s) := by
  rw [thingCall_checked,thingPrepare_checked]
  exact OriginalThingCallback.resume_execution s f
"""
    return source+'\n'.join('#print axioms '+n for n in NAMES)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.OriginalThingCallback.'+n for n in GENERIC)+'\n'+'\n'.join(
        '#print axioms Doom.Proofs.E1M1ThingCallback.'+n for n in PROOFS)+'\nend Doom.Verification.ExtractedThingCallback\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingCallback.thingCall_checked'"
    require(marker in output, 'missing thing-callback certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingCallback.'+n for n in NAMES]+[
            'Doom.Proofs.OriginalThingCallback.'+n for n in GENERIC]+[
            'Doom.Proofs.E1M1ThingCallback.'+n for n in PROOFS]:
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
    out = ROOT/'artifacts/e1m1-thing-callback'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingCallback'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='Two additional pinned DOS ranges prove the indirect object callback call, '
                        'six register saves and local allocation, and callback-return stop/next/null decisions. '
                        'With explicit nonempty first-cell and stack separation contracts, the continuous '
                        'firing prefix reaches the object intersection body at 0x2c72b, preserving line '
                        'intercepts, object argument, saved list pointer and callback return word; bound '
                        '413+281*list_length. Resume uses post-callback memory. Callback intersection body, '
                        'epilogue, list traversal, reachable-state discharge, later cells, damage and '
                        'whole-tic correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original object callback handoff and return-side list decision; strict axiom audit.')


if __name__ == '__main__':
    main()

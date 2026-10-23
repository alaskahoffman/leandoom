#!/usr/bin/env python3
"""Certify firing-entry geometry transport and the DOS object crossing gate."""
import json
import re
import subprocess
import verify_e1m1_thing_first_side as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1ThingGeometry': ['scan_read', 'entry_frame', 'object_read', 'trace_read', 'callback_inputs', 'firing_live'], 'OriginalThingSecondSide': ['decoded', 'contains_prior', 'contains_local', 'call_execution', 'test_execution', 'apart', 'call_observe', 'second_returned', 'execution', 'call_frame', 'helper_safe', 'tested_observe', 'frame', 'side_safe', 'second_inputs', 'bit_eq', 'live'], 'E1M1ThingCrossing': ['contains_prior', 'contains_local', 'contains_second', 'collection', 'firing_crossing']}
SEGMENTS = ["thingSecond"]
NAMES = ["thingSecond_checked","execution_checked"]


def extracted():
    import verify_original_inline_thrust as extraction
    spec, profile, raw = previous.extracted()
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    part = json.loads((ROOT/'tests/reference/original-thing-second.json').read_text())
    require(part['exe_profile']=='original-mul.json','unexpected executable profile')
    extra = extraction.extract(binary,profile,part)
    require(not(set(spec['units']) & set(extra)),'conflicting thing code range')
    return dict(units={**spec['units'],**part['units']}),profile,{**raw,**extra}


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingCrossing\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingCrossing
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
"""
    for name in SEGMENTS:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Bytes=OriginalThingSecondSide.'+name+' := by decide\n'
    source+="""def extractedProgram : X86Routine.Program := fun pc =>
  match OriginalThingFirstSide.program pc with
  | some op => some op
  | none => OriginalThingSecondSide.bytesProgram thingSecondBytes pc
theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤53, X86Routine.Prefix extractedProgram
      [] n ⟨s,f,0x2c78d⟩ (OriginalThingSecondSide.result s) := by
  unfold extractedProgram
  rw [thingSecond_checked]
  exact OriginalThingSecondSide.execution s f
"""
    source+='\n'.join('#print axioms '+n for n in NAMES)+'\n'
    for module,names in GROUPS.items():
        source+='\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source+'end Doom.Verification.ExtractedThingCrossing\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingCrossing.thingSecond_checked'"
    require(marker in output, 'missing thing-crossing certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingCrossing.'+n for n in NAMES]+[
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
    out = ROOT/'artifacts/e1m1-thing-crossing'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingCrossing'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='One additional authenticated DOS range proves the second endpoint CALL and '
                        'equal-side skip versus crossing-fraction branch. Initial firing-state object '
                        'coordinates/radius and initialized trace facts are transported through the first '
                        'cell line scan and object callback. Equal endpoint sides imply the actual Lean '
                        'thingIntercept returns no hit. Joined execution from either weapon post-sound '
                        'entry reaches the branch within 533+281*list_length instructions and preserves '
                        'existing line intercepts. Initial memory representation/separation are hypotheses. '
                        'Crossing fraction, object append/epilogue/list traversal, later cells, reachable '
                        'world-state discharge, damage, and whole-tic/render/audio correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: firing-entry geometry and original object crossing gate; strict axiom audit.')


if __name__ == '__main__':
    main()

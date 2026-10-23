#!/usr/bin/env python3
"""Certify DOS object append, epilogue, and post-callback traversal continuation."""
import json
import re
import subprocess
import verify_e1m1_thing_fraction as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalThingFinish': ['decoded', 'unwind_execution', 'insert_execution', 'unwind_observe', 'inserted_memory', 'inserted_regs', 'execution', 'result_memory', 'result_value', 'result_sp', 'result_cursor', 'result_pc', 'written_frame', 'frame', 'written_cursor', 'written_record', 'append_encoded', 'append_tracks'], 'E1M1ThingReturn': ['contains_prior', 'contains_finish', 'contains_resume', 'fraction_regs', 'view_regs', 'view_saved', 'returned', 'outcome_finish', 'execution'], 'E1M1ThingFinish': ['step_lines', 'run_lines', 'finished_lines', 'relabel', 'metadata', 'finish_collect', 'firing_finish']}
SEGMENTS = ["thingFinish"]
NAMES = ["thingFinish_checked","execution_checked"]


def extracted():
    import verify_original_inline_thrust as extraction
    spec, profile, raw = previous.extracted()
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    part = json.loads((ROOT/'tests/reference/original-thing-finish.json').read_text())
    require(part['exe_profile']=='original-mul.json','unexpected executable profile')
    extra = extraction.extract(binary,profile,part)
    require(not(set(spec['units']) & set(extra)),'conflicting thing code range')
    return dict(units={**spec['units'],**part['units']}),profile,{**raw,**extra}


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingFinish\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingFinish
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
"""
    for name in SEGMENTS:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Bytes=OriginalThingFinish.'+name+' := by decide\n'
    source+="""theorem execution_checked (s : X86Control.State)
    (atFinish : s.pc∈[0x2c7da,0x2c7e4,0x2c805]) :
    ∃ n≤15, X86Routine.Prefix (OriginalThingFinish.bytesProgram thingFinishBytes)
      [] n s (OriginalThingFinish.result s) := by
  rw [thingFinish_checked]
  exact OriginalThingFinish.execution s atFinish
"""
    source+='\n'.join('#print axioms '+n for n in NAMES)+'\n'
    for module,names in GROUPS.items():
        source+='\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source+'end Doom.Verification.ExtractedThingFinish\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingFinish.thingFinish_checked'"
    require(marker in output, 'missing thing-finish certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingFinish.'+n for n in NAMES]+[
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
    out = ROOT/'artifacts/e1m1-thing-finish'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingFinish'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='One additional authenticated DOS range covers object record writes, cursor '
                        'advance and both epilogues. The existing collection gains exactly the production '
                        'optional object intercept in order, with the object flag zero and actor pointer. '
                        'Line-only preservation derives the mixed pointer resolver. Callback saved words '
                        'survive geometry and the proved return restores the object cursor before reading '
                        'the post-callback link. Common post-sound firing entry reaches the next-object '
                        'or end-of-list decision within 633+281*list_length instructions. Initial memory '
                        'representation, arithmetic success, an available intercept slot, object-ID mapping '
                        'and stack/array separation remain contracts. Full linked-list iteration, iterator '
                        'epilogue, later cells, reachable-state discharge, damage and whole-tic/observable '
                        'equivalence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original object append, return and traversal continuation; strict axiom audit.')


if __name__ == '__main__':
    main()

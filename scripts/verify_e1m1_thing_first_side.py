#!/usr/bin/env python3
"""Certify the original object diagonal choice and first point-side calculation."""
import json
import re
import subprocess
import verify_e1m1_thing_callback as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'OriginalThingDiagonal': ['decoded', 'gate_execution', 'p_execution', 'n_execution', 'diagonal_execution', 'call_execution', 'first_execution', 'diagonal_observe', 'first_observe', 'first_frame', 'production', 'live_diagonal'], 'OriginalThingFirstSide': ['contains_diagonal', 'contains_side', 'execution', 'helper_safe', 'frame', 'returned', 'second_endpoint', 'helper_inputs', 'live'], 'E1M1ThingFirstSide': ['contains_prior', 'contains_first_side', 'collection', 'firing_first_side']}
SEGMENTS = ["thingDiagonal"]
NAMES = ["thingDiagonal_checked","execution_checked"]


def extracted():
    import verify_original_inline_thrust as extraction
    spec, profile, raw = previous.extracted()
    share = json.loads((ROOT/'tests/reference/shareware.json').read_text())
    binary = extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
    part = json.loads((ROOT/'tests/reference/original-thing-diagonal.json').read_text())
    require(part['exe_profile']=='original-mul.json','unexpected executable profile')
    extra = extraction.extract(binary,profile,part)
    require(not(set(spec['units']) & set(extra)),'conflicting thing code range')
    return dict(units={**spec['units'],**part['units']}),profile,{**raw,**extra}


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1ThingFirstSide\n'+previous.certificate(data, raw)
    source += """namespace Doom.Verification.ExtractedThingFirstSide
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
"""
    for name in SEGMENTS:
        source+='def '+name+'Bytes : List UInt8 := ['+','.join(hex(b) for b in raw[name])+']\n'
        source+='theorem '+name+'_checked : '+name+'Bytes=OriginalThingDiagonal.'+name+' := by decide\n'
    source+="""theorem execution_checked (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤23, X86Routine.Prefix (OriginalThingDiagonal.bytesProgram thingDiagonalBytes)
      [] n ⟨s,f,0x2c72b⟩ (OriginalThingDiagonal.first s) := by
  rw [thingDiagonal_checked]
  exact OriginalThingDiagonal.first_execution s f
"""
    source+='\n'.join('#print axioms '+n for n in NAMES)+'\n'
    for module,names in GROUPS.items():
        source+='\n'.join('#print axioms Doom.Proofs.'+module+'.'+n for n in names)+'\n'
    return source+'end Doom.Verification.ExtractedThingFirstSide\n'


def audit(output):
    marker="'Doom.Verification.ExtractedThingFirstSide.thingDiagonal_checked'"
    require(marker in output, 'missing thing-first-side certificate audit')
    before, rest = output.split(marker, 1)
    previous.audit(before)
    rest = (marker+rest).strip()
    for name in ['Doom.Verification.ExtractedThingFirstSide.'+n for n in NAMES]+[
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
    out = ROOT/'artifacts/e1m1-thing-first-side'
    out.mkdir(parents=True, exist_ok=True)
    source = out/'Checked.lean'
    source.write_text(certificate(data, raw))
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.E1M1ThingFirstSide'], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(source)],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report = dict(wad_sha256=map_profile['wad_sha256'], exe_sha256=profile['exe_sha256'],
                  units=spec['units'], cells=len(data['cells']), axioms=checked.stdout.splitlines(),
                  scope='One additional authenticated DOS range proves signed-XOR diagonal selection, '
                        'both endpoint constructions and the first point-side CALL. The existing full '
                        'divline-side proof supplies the first Boolean side result under explicit object/trace '
                        'memory representation and separation. A definitional equation ties these endpoints '
                        'to the live object-intercept function. Continuous first-cell firing execution reaches '
                        '0x2c78d within 480+281*list_length instructions and preserves collected line intercepts. '
                        'Object/trace representation transport from initial firing memory, the second endpoint '
                        'test, crossing fraction, object collection/epilogue/list traversal and whole-tic '
                        'correspondence remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: original object diagonal and first-side calculation; strict axiom audit.')


if __name__ == '__main__':
    main()

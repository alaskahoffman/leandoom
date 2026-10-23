#!/usr/bin/env python3
"""Certify the second line return and continuous entry into the next object iterator."""
import json
import re
import subprocess
import verify_e1m1_firing_next_lines as previous
ROOT, require = previous.ROOT, previous.require
GROUPS = {'E1M1NextLineReturn': ['read_word', 'parent_return', 'flag_word'], 'E1M1NextSavedFrame': ['flag_safe', 'saved_words', 'flag_word'], 'E1M1FiringNextThings': ['enter', 'execution']}
extracted = previous.extracted
pinned_data = previous.pinned_data


def certificate(data, raw):
    source = 'import Doom.Proofs.E1M1FiringNextThings\n'+previous.certificate(data,raw)
    for module,names in GROUPS.items():
        source += '\n'.join('#print axioms Doom.Proofs.'+module+'.'+name for name in names)+'\n'
    return source


def audit(output):
    marker = "'Doom.Proofs.E1M1NextLineReturn.read_word'"
    require(marker in output,'missing firing next-things audit')
    before,rest=output.split(marker,1)
    previous.audit(before)
    rest=(marker+rest).strip()
    for module,names in GROUPS.items():
        for name in names:
            full='Doom.Proofs.'+module+'.'+name
            match=re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
            require(match is not None,'missing audit: '+full)
            axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
            require(axioms <= {'propext','Quot.sound','Classical.choice'},'unexpected axioms')
            rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    data,map_profile=pinned_data()
    spec,profile,raw=extracted()
    require(profile['exe_sha256']==map_profile['exe_sha256'],'executable profile mismatch')
    out=ROOT/'artifacts/e1m1-firing-next-things'
    out.mkdir(parents=True,exist_ok=True)
    source=out/'Checked.lean'
    source.write_text(certificate(data,raw))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1FiringNextThings'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(source)],cwd=ROOT,
                           capture_output=True,text=True,timeout=120)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode==0,'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    report=dict(wad_sha256=map_profile['wad_sha256'],exe_sha256=profile['exe_sha256'],
                units=spec['units'],cells=len(data['cells']),axioms=checked.stdout.splitlines(),
                scope='Same 29 authenticated DOS byte ranges. The second line iterator '
                      'preserves its real saved EDI and return address, restores the '
                      'caller stack, and returns success to 0x2ca94. Saved words derive '
                      'from CALL/prologue, not assumed reached memory. The initialized '
                      'option word survives; the success test, object-enable gate and '
                      'real CALL enter P_BlockThingsIterator at 0x2c5a0, with callback '
                      '0x2c720 and return word 0x2cab1. The continuous post-sound bound '
                      'is 482 + 281*(first_line_count + next_tail_count) + '
                      '230*first_object_count. Mixed hits, exact prior-hit order and '
                      'updated visited history survive the CALL. Initial contracts and '
                      'the two-cell candidate budget remain explicit. This stops before '
                      'object table lookup: identifying retained call coordinates with '
                      'the next map cell, its list/callback execution, repeated-cell '
                      'capacity/induction, production outer-loop correspondence, clipping, '
                      'damage and full query/tic remain open. Runtime and instruction '
                      'semantics are unchanged.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: next line return and object CALL joined to firing prefix; strict transitive axiom audit.')


if __name__=='__main__':main()

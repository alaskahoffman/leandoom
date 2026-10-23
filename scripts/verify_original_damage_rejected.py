#!/usr/bin/env python3
"""Certify rejected damage returns and the combined nonlethal CALL/RET theorem."""
import argparse
import json
import re
import subprocess
import verify_original_damage_return as previous

ROOT, require = previous.ROOT, previous.require
NAMES=[name+'_checked' for name in previous.UNITS]+['live_checked']+[
    'Doom.Proofs.DamageRejected.'+name for name in
    ['execution','original_execution','memory_unchanged','rejected_live','rejected_prefix',
     'contains_entry','joined_execution','accepted_observation','initial_observation',
     'nonlethal_execution','live_correspondence']]


def certificate(raw,digest):
    source=previous.certificate(raw,digest)
    source=source[:source.index('#print axioms')]
    source=source.replace('import Doom.Proofs.OriginalDamageReturn','import Doom.Proofs.OriginalDamageRejected')
    source=source.replace('ExtractedDamageReturn','ExtractedDamageRejected')
    source=source.replace('open Doom.Proofs DamageReturn','open Doom.Proofs DamageRejected')
    source=source.replace('tail = code','tail = DamageReturn.code')
    source=source.replace('(h : JoinedInputs s v d baby rngState.play)','(h : Inputs s v d baby rngState.play)')
    source=source.replace('    (applied : (Doom.PlayerDamage.apply v d none false baby rngState).applied = true)\n','')
    source=source.replace('then bytesProgram tail pc','then DamageReturn.bytesProgram tail pc')
    source=source.replace('      exits 166','      DamageReturn.exits 166')
    source=source.replace('h applied alive','h alive')
    return source+'\n'.join('#print axioms '+name for name in NAMES)+'\nend Doom.Verification.ExtractedDamageRejected\n'


def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedDamageRejected.'+short
        match=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None,'missing axiom audit: '+name)
        axioms={a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axioms: '+str(axioms))
        rest=rest[match.end():].strip()
    require(not rest,'unexpected certificate output')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check',action='store_true');args=parser.parse_args()
    spec=json.loads((ROOT/'tests/reference/original-damage-return.json').read_text())
    profile=json.loads((ROOT/'tests/reference'/spec['exe_profile']).read_text())
    sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    extraction=previous.extraction
    binary=extraction.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
    raw=extraction.extract(binary,profile,spec)
    raw['painState']=previous.table_data(binary,profile,spec)
    import verify_original_arithmetic as arithmetic
    arithmetic_spec=json.loads((ROOT/'tests/reference/original-arithmetic.json').read_text())
    raw['table']=arithmetic.verify_units(binary,profile,arithmetic_spec)['randomTableBytes']
    out=ROOT/'artifacts/original-damage-rejected';out.mkdir(parents=True,exist_ok=True)
    path=out/'Extracted.lean';path.write_text(certificate(raw,profile['exe_sha256']))
    subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalDamageRejected','player-damage-probe'],cwd=ROOT,check=True)
    checked=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True,check=True)
    audit(checked.stdout)
    report={'exe_sha256':profile['exe_sha256'],'axioms':checked.stdout.splitlines(),
            'scope':'Original floor damage CALL through RET for all nonlethal outcomes, under initial relations. Rejected memory is exactly the real prologue saved memory; gameplay/RNG/timers/attacker preserved with stack separation. Accepted survivors reuse the existing return proof. Lethal handling and whole-tic/game correspondence remain open.',
            'cross_check':previous.cross_check(raw,spec,return_rejected=True) if args.cross_check else None}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if args.cross_check:(out/'cross-check.json').write_text(json.dumps(report['cross_check'],indent=2)+'\n')
    print(f'PASS: nonlethal damage returns; {len(NAMES)} audited declarations.')
    if args.cross_check:print('Continuous original-byte/live-apply comparisons:',report['cross_check'])

if __name__=='__main__':
    try:main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or '');print(error.stderr or '');raise

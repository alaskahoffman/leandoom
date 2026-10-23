#!/usr/bin/env python3
"""Authenticated all-four-byte-aligned memset, original entry and exact frames.
Not cache/read/gate completion or initialized startup.
"""
import argparse
import json
import re
import subprocess
import sys
from typing import Any
sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
import verify_e1m1_aim_word_fill as previous
import verify_e1m1_aim_side_entry as extraction
ROOT, require = previous.ROOT, previous.require
MODULE = 'E1M1AimWordAligned'
NS = 'Doom.Verification.ExtractedAimWordAligned'
HEADER = 'open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimWordFill E1M1AimWordAligned\n'

def contracts():
    return re.findall(r'^theorem (\w+) ', (ROOT/f'Doom/Proofs/{MODULE}.lean').read_text(), re.M)

def names():
    return [NS+'.program_checked'] + [full for name in contracts() for full in
        [NS+'.'+name+'_checked', 'Doom.Proofs.'+MODULE+'.'+name]]

def certificate():
    source = 'import Doom.Proofs.E1M1AimWordAligned\n'+previous.certificate()
    imports = list(dict.fromkeys(re.findall(r'^import .+$', source, re.M)))
    source = '\n'.join(imports)+'\n'+re.sub(r'^import .+\n', '', source, flags=re.M)
    source += '\nnamespace '+NS+'\n'+HEADER
    source += 'def program := Doom.Verification.ExtractedAimWordFill.program\n'
    source += 'theorem program_checked : program=E1M1AimWordFill.program := by\n  exact Doom.Verification.ExtractedAimWordFill.program_checked\n'
    for name in contracts():
        decl, args = extraction.contract(MODULE, name)
        decl = re.sub(r'(?<![\w.])Knowledge\b', 'Doom.Verification.X86WordFillRoutine.Knowledge', decl)
        for token in ['listed', 'doneCore', 'Saved32Safe', 'Entry32Safe', 'OutputSafe', 'zeros']:
            decl = re.sub(r'(?<![\w.])'+token+r'\b', 'Doom.Proofs.E1M1AimWordFill.'+token, decl)
        decl = decl.replace('theorem '+name, 'theorem '+name+'_checked', 1)
        changed = re.sub(r'(?<![\w.])program\b', NS+'.program', decl)
        source += changed+' := by\n'
        if changed != decl:
            source += '  simp only ['+NS+'.program_checked]\n'
        source += '  exact Doom.Proofs.'+MODULE+'.'+name+' '+args+'\n'
    source += 'end '+NS+'\n'
    return source+'\n'.join('#print axioms '+n for n in names())+'\n'

def audit(output):
    marker = "'"+names()[0]+"'"
    require(marker in output, 'missing aligned audit')
    inherited, rest = output.split(marker, 1)
    previous.audit(inherited)
    rest = (marker+rest).strip()
    for full in names():
        m = re.match(re.escape(f"'{full}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)', rest)
        require(m is not None, 'missing audit: '+full)
        assert m is not None  # narrow after the non-optional runtime guard
        require({a.strip() for a in (m[1] or '').split(',') if a.strip()} <=
                {'propext', 'Quot.sound', 'Classical.choice'}, 'unexpected axioms')
        rest = rest[m.end():].strip()
    require(not rest, 'unexpected certificate output')

def cross_check():
    native: dict[str, Any] = dict(full_memset=previous.previous.cross_check(), partial_flags=previous.flag_cross_check())
    native['full_memset']['universal_memset_theorem'] = True
    native['full_memset']['formal_alignment_bytes'] = 4
    native['full_memset']['scope'] = ('Constructed directory/heap placements, continuous actual entry0x2e3e0 through allocation, publication and complete nested memset to0x2e437. All cases are independently CPU-checked; the four-byte-aligned subset is now also covered universally by entry_execution under static initial guards. Other alignments remain empirical. Not reached DOS heap history or initialized startup.')
    details = native['full_memset']['details']
    aligned = [c for c in details if (c['alignment']+24)%4 == 0]
    native['formal_4byte_destination_cases'] = len(aligned)
    native['formal_32byte_destination_cases'] = sum((c['alignment']+24)%32 == 0 for c in details)
    native['head_counts'] = sorted({(-(c['alignment']+24)%32)//4 for c in aligned})
    native['word_tails'] = sorted({(2916-(-(c['alignment']+24)%32)//4)%4 for c in aligned})
    require(native['head_counts'] == list(range(8)), 'missing alignment head cases')
    require(native['word_tails'] == list(range(4)), 'missing residual tail cases')
    native['formal_scope'] = 'All four-byte-aligned destinations, universally under initial static guards; constructed CPU fixtures are not reached DOS history.'
    return native

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cross-check', action='store_true')
    args = ap.parse_args()
    out = ROOT/'artifacts/e1m1-aim-word-aligned'
    out.mkdir(exist_ok=True)
    (out/'Checked.lean').write_text(certificate())
    subprocess.run([str(ROOT/'scripts/lake'), 'build', 'Doom.Proofs.'+MODULE], cwd=ROOT, check=True)
    checked = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(out/'Checked.lean')],
                             cwd=ROOT, capture_output=True, text=True, timeout=300)
    (out/'axioms.log').write_text(checked.stdout+checked.stderr)
    require(checked.returncode == 0, 'certificate failed: '+checked.stdout+checked.stderr)
    audit(checked.stdout)
    require(not checked.stderr.strip(), 'unexpected stderr')
    native = None
    if args.cross_check:
        native = cross_check()
        (out/'cross-check.json').write_text(json.dumps(native, indent=2)+'\n')
    elif (out/'cross-check.json').exists():
        native = json.loads((out/'cross-check.json').read_text())
    prior = json.loads((ROOT/'artifacts/e1m1-aim-word-fill/report.json').read_text())
    audits = re.findall(r"^'([^']+)'", checked.stdout, re.M)
    unique = {(int(v['code_offset'],16), len(bytes.fromhex(v['hex']))) for v in prior['units'].values()}
    report = dict(exe_sha256=prior['exe_sha256'], wad_sha256=prior['wad_sha256'], units=prior['units'],
        unique_ranges=len(unique), public_theorems=len(contracts()), audited_declarations=len(audits),
        unique_audited_declarations=len(set(audits)), cross_check=native,
        scope='Continuous original entry0x2e3e0 through length, allocation, publication, all0..7 head stores, existing group induction, actual0..3 word tails, and all three RETs to0x2e437 in at most5300 instructions. Every11664 byte zero for every four-byte-aligned destination under old initial heap/catalog/stack separations. Late count PUSH commuted only under proved static separation. Exact registers and arbitrary protected-word frames. No reached image/helper-success assumption. Cache/read/gate and initialized-startup relation remain open.')
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: universal full four-byte-aligned memset and original-entry frames; startup remains incomplete.')

if __name__ == '__main__':
    main()

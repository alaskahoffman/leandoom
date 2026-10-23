#!/usr/bin/env python3
"""Derive counting-to-allocation contracts from initial raw heap headers."""
import json
import re
import subprocess
import verify_original_group_malloc as malloc

ROOT, require = malloc.ROOT, malloc.require
NS = 'Doom.Verification.ExtractedGroupHeap.'
NAMES = malloc.NAMES + [NS+'ready_checked', NS+'startup_checked'] + [
    'Doom.Proofs.OriginalGroupHeap.'+name for name in [
        'View.transport','View.fields','prefix_frame','saved_view','candidate_fields',
        'successor','split_safe','ready','count_view','count_ready','execution']]


def certificate(raw):
    source = malloc.certificate(raw).replace('import Doom.Proofs.OriginalGroupStartup',
                                           'import Doom.Proofs.OriginalGroupHeap')
    source += '''namespace Doom.Verification.ExtractedGroupHeap
open X86 X86Memory X86Control Doom.Proofs

theorem ready_checked (v : OriginalGroupHeap.View) (s : X86Memory.State)
    (heap : v.Holds s.memory)
    (conditions : OriginalGroupHeap.Conditions v (s.regs 0) (s.regs 4)) :
    OriginalGroupMalloc.Ready s := OriginalGroupHeap.ready v s heap conditions

theorem startup_checked (v : OriginalGroupHeap.View)
    (es : List OriginalGroupOutput.Line) (s : X86Memory.State) (f : Option Flags)
    (small : es.length<2147483648) (layout : OriginalGroupCountScan.Layout es)
    (inputs : OriginalGroupOutput.Inputs es s.memory)
    (linked : OriginalGroupOutput.Linked es (load32 s.memory 0x2c120))
    (count : (load32 s.memory 0x2c134).toNat=es.length)
    (heap : v.Holds s.memory)
    (safe : ∀ w∈v.words, OriginalGroupCountScan.SafeWord w.1 es)
    (conditions : OriginalGroupHeap.Conditions v (OriginalGroupHeap.request es) (s.regs 4)) :
    X86Routine.run ExtractedGroupMalloc.startupProgram [0x2e661,0x2e791]
      (87+17*es.length) ⟨s,f,0x2e5ef⟩=some (OriginalGroupStartup.result es s) := by
  rw [ExtractedGroupMalloc.startup_program_checked]
  exact OriginalGroupHeap.execution v es s f small layout inputs linked count heap safe conditions
'''
    source += '\n'.join('#print axioms '+name for name in NAMES[len(malloc.NAMES):])
    return source+'\nend Doom.Verification.ExtractedGroupHeap\n'


def audit(output):
    rest = output.strip()
    for name in NAMES:
        match = re.match(re.escape(f"'{name}'")+
                         r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(match is not None, 'missing audit: '+name)
        axioms = {a.strip() for a in (match[1] or '').split(',') if a.strip()}
        require(axioms <= {'propext','Quot.sound','Classical.choice'}, 'unexpected axioms: '+str(axioms))
        rest = rest[match.end():].strip()
    require(not rest, 'unexpected certificate output')


def main():
    raw, profile, _ = malloc.extracted()
    out = ROOT/'artifacts/original-group-heap'
    out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.OriginalGroupHeap'],cwd=ROOT,
                       stdout=log,stderr=subprocess.STDOUT,check=True)
    path = out/'Checked.lean'
    path.write_text(certificate(raw))
    result = subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,
                            capture_output=True,text=True,timeout=90)
    if result.returncode:
        print(result.stdout); print(result.stderr); result.check_returncode()
    audit(result.stdout)
    require(not result.stderr.strip(), 'unexpected stderr')
    (out/'report.json').write_text(json.dumps(dict(
        exe_sha256=profile['exe_sha256'],audited_declarations=len(NAMES),
        axioms=result.stdout.splitlines(),
        scope='Raw initial heap header and separation conditions derive allocator readiness after counting. '
              'Same pinned instruction path; no new native cross-check. Initial heap construction, '
              'general search/purge, and whole startup remain open.'),indent=2)+'\n')
    print(result.stdout,end='')
    print('PASS: initial raw heap facts establish counting-to-allocation contracts.')


if __name__=='__main__': main()

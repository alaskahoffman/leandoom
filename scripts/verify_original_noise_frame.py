#!/usr/bin/env python3
"""Audit sound-frame provenance and progress, rechecking the original-byte chain."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['frame_checked','child_checked','progress_checked']
NAMES+=['Doom.Proofs.E1M1NoiseFrame.'+n for n in [
    'prepared_memory','saved_words','prepared_saved','Saved.then_frame','restores',
    'sector_saved','child_restores','child_progress','remaining_decreases','terminal_child_execution']]

def certificate():
    s='''import Doom.Proofs.E1M1NoiseFrame
namespace Doom.Verification.ExtractedNoiseFrame
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary E1M1NoiseFrame
theorem frame_checked (entry s t : X86Memory.State) (h : Saved entry s)
    (sp : t.regs 4=s.regs 4) (writes : List Word)
    (frame : PlayerHeight.Frame s.memory t.memory writes)
    (safe : ∀ a, a ∈ slots entry → ∀ b, b ∈ writes → Apart a b) : Saved entry t :=
  h.then_frame sp writes frame safe
theorem child_checked (parent : X86Memory.State) (f : Option Flags)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core)
    (terminal : (E1M1NoiseAlert.sectorResult (NoiseTraversal.recursiveCall parent f).core).pc=0x27011) :
    E1M1NoiseRecursive.Runs 36 (NoiseTraversal.recursiveCall parent f)
      (NoiseTraversal.advanced (E1M1NoiseTraversal.sectorReturn (NoiseTraversal.recursiveCall parent f).core).core) :=
  terminal_child_execution parent f safe terminal
theorem progress_checked (s : X86Memory.State) (n : Nat)
    (index : (s.regs 6).toNat<n) (small : n≤2147483647) :
    n-((NoiseTraversal.advanced s).core.regs 6).toNat < n-(s.regs 6).toNat :=
  remaining_decreases s n index small
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseFrame\n'

def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseFrame.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms))
        rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')

def main():
    out=ROOT/'artifacts/original-noise-frame';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-recursive')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseFrame'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-recursive/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],
        audited_declarations=len(NAMES),axioms=r.stdout.splitlines(),
        scope='Saved sound frames, separated sector-prefix writes, exact child restoration and local loop progress. Full recursive frame preservation, termination and production worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: sound-frame provenance, separated restoration and local progress.')
if __name__=='__main__':main()

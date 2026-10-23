#!/usr/bin/env python3
"""Verify recursive sound write footprints, frame restoration and continuation."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['frame_checked','restore_checked','child_checked','progress_checked']
NAMES+=['Doom.Proofs.E1M1NoiseFootprint.'+n for n in ['frame_trans','sector_sp','sector_frame','opening_sp','dispatch_sp','dispatch_frame']]
NAMES+=['Doom.Proofs.E1M1NoisePreservation.'+n for n in ['of_eval','Trace.frame','finish_view','Trace.view','Trace.restores_lines','Trace.restores_sector','eval_restores','eval_frame','child_remaining','eval_child_returns','child_execution']]
def certificate():
    s='''import Doom.Proofs.E1M1NoisePreservation
namespace Doom.Verification.ExtractedNoisePreservation
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoisePreservation
theorem frame_checked (k : Nat) (phase : Phase) (s t : X86Control.State)
    (run : eval k phase s=some t) : PlayerHeight.Frame s.core.memory t.core.memory (writes k phase s) :=
  eval_frame k phase s t run
theorem restore_checked (k : Nat) (s t : X86Control.State)
    (run : eval k .sector s=some t) (safe : SectorSafe s.core (writes k .sector s)) : Restored s.core t :=
  eval_restores k s t run safe
theorem child_checked (k : Nat) (parent : X86Memory.State) (f : Option Flags) (t : X86Control.State)
    (run : eval k .sector (NoiseTraversal.recursiveCall parent f)=some t)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core
      (writes k .sector (NoiseTraversal.recursiveCall parent f))) :
    Runs (bound k+5) (NoiseTraversal.recursiveCall parent f) (advance t) :=
  child_execution k parent f t run safe
theorem progress_checked (k : Nat) (parent : X86Memory.State) (f : Option Flags) (t : X86Control.State) (n : Nat)
    (run : eval k .sector (NoiseTraversal.recursiveCall parent f)=some t)
    (safe : SectorSafe (NoiseTraversal.recursiveCall parent f).core
      (writes k .sector (NoiseTraversal.recursiveCall parent f)))
    (index : (parent.regs 6).toNat<n) (small : n≤2147483647) :
    n-((advance t).core.regs 6).toNat < n-(parent.regs 6).toNat :=
  child_remaining k parent f t n run safe index small
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoisePreservation\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoisePreservation.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-preservation';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-frame')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoisePreservation'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-frame/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='All successful recursive sound evaluations have proved conservative write footprints and return-stack views. Separation of the computed footprint implies saved-register/return restoration and child continuation. Reachable-state separation, termination/sufficient fuel and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: recursive sound footprint, frame restoration and child continuation.')
if __name__=='__main__':main()

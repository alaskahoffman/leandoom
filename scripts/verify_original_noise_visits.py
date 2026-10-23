#!/usr/bin/env python3
"""Verify original sound admissions, finite-ledger revisit budget and stable marks."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['gate_checked','progress_checked','budget_checked','stable_checked']
NAMES+=['Doom.Proofs.E1M1NoiseVisits.'+n for n in ['gate_admits','admitted_decreases','update_rep','machine_progress','sector_more_progress','child_count','Admission.decreases','potential_bound','Admissions.budget','Admissions.at_most_twice','machine_admission','prepared_generation','prepared_inputs','sector_progress','Rep.frame','update_other_mark','eval_preserves_mark','eval_preserves_generation']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseVisits
namespace Doom.Verification.ExtractedNoiseVisits
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseVisits
theorem gate_checked (s : X86Memory.State) (m : Mark) (b : Bool) (h : GateInputs s m b) :
    (NoiseAlert.gate s).pc=0x26f83 ↔ admits m b=true := gate_admits s m b h
theorem progress_checked (s : X86Memory.State) (m : Mark) (b : Bool)
    (rep : Rep (load32 s.memory (0x13580#32)) (s.regs 0) s.memory m)
    (count : s.regs 2=blocks b) (safe : PrologueSafe s)
    (more : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6) :
    Rep ((NoiseAlert.prepared s).regs 2) ((NoiseAlert.prepared s).regs 3)
      (E1M1NoiseAlert.sectorResult s).core.memory (marked b) ∧ rank (marked b)+1≤rank m :=
  sector_progress s m b rep count safe more
theorem budget_checked (xs ys : List Mark) (n : Nat) (h : Admissions xs ys n) : n≤2*xs.length :=
  h.at_most_twice
theorem stable_checked (k : Nat) (phase : E1M1NoiseRecursive.Phase) (s t : X86Control.State)
    (run : E1M1NoiseRecursive.eval k phase s=some t)
    (safe : ∀ b, b ∈ E1M1NoisePreservation.writes k phase s → BlockSummary.Apart (0x13580#32) b) :
    load32 t.core.memory (0x13580#32)=load32 s.core.memory (0x13580#32) :=
  eval_preserves_generation k phase s t run safe
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseVisits\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseVisits.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-visits';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-preservation')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseVisits'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-preservation/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Original gate/update refinement and finite-ledger two-admissions-per-sector budget. Preservation of untouched marks and generation follows from separated writes. A complete recursive ledger invariant, sufficient fuel and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original sound admission, two-credit revisit budget and stable marks.')
if __name__=='__main__':main()

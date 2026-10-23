#!/usr/bin/env python3
"""Verify whole-ledger sound traversal accounting and finite-trace adequacy."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['ledger_checked','budget_checked','fuel_checked','execution_checked']
NAMES+=['Doom.Proofs.E1M1NoiseLedger.'+n for n in ['update_addresses','update_credit','prepared_frame','sector_step','sector_more_charge','line_step']]
NAMES+=['Doom.Proofs.E1M1NoiseTraceFuel.'+n for n in ['eval_succ','eval_mono','trace_evaluates']]
NAMES+=['Doom.Proofs.E1M1NoiseAccounting.CheckedTrace.'+n for n in ['trace','accounting','admission_bound','frame','restores_sector','evaluates','execution']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseAccounting
namespace Doom.Verification.ExtractedNoiseAccounting
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoiseLedger E1M1NoiseAccounting
theorem ledger_checked (layout : List Word) (generation : Word) (s : X86Memory.State) (xs : Ledger)
    (shape : addresses xs=layout) (rep : Represents generation s.memory xs) (safe : SectorSafe layout s) :
    ∃ ys, addresses ys=layout ∧ Represents generation (E1M1NoiseAlert.sectorResult s).core.memory ys ∧
      credit ys+charge s≤credit xs := sector_step layout generation s xs shape rep safe
theorem budget_checked (layout : List Word) (phase : Phase) (s t : X86Control.State) (w : List Word) (n : Nat)
    (h : CheckedTrace layout phase s t w n) (generation : Word) (xs : Ledger)
    (shape : addresses xs=layout) (rep : Represents generation s.core.memory xs) : n≤2*layout.length :=
  h.admission_bound generation xs shape rep
theorem fuel_checked (k j : Nat) (phase : Phase) (s t : X86Control.State)
    (le : k≤j) (run : eval k phase s=some t) : eval j phase s=some t :=
  E1M1NoiseTraceFuel.eval_mono k j phase s t le run
theorem execution_checked (layout : List Word) (phase : Phase) (s t : X86Control.State) (w : List Word) (n : Nat)
    (h : CheckedTrace layout phase s t w n) (pc : s.pc=phase.pc) : ∃ k, Runs (bound k) s t := h.execution pc
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseAccounting\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseAccounting.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-accounting';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-visits')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseAccounting'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-visits/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Original finite recursive traversal preserves a whole sector ledger and spends its credit on admissions, under explicit local address/count guards. At most twice the ledger sector count admissions. Every checked finite trace is realized by the evaluator and original instruction model; additional fuel preserves a completed result. Reachability of all guards, map-derived sufficient fuel/termination and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: whole-ledger sound accounting, recursive admission bound and finite-trace adequacy.')
if __name__=='__main__':main()

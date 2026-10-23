#!/usr/bin/env python3
"""Verify original line progress and an explicit conditional traversal fuel bound."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['dispatch_checked','advance_checked','child_checked','budget_checked','execution_checked']
NAMES+=['Doom.Proofs.E1M1NoiseLineProgress.'+n for n in ['opening_regs','opened_regs','dispatch_regs','start_remaining','map_word','advance_remaining','skip_remaining','child_remaining']]
NAMES+=['Doom.Proofs.E1M1NoiseFuelBound.'+n for n in ['bounded_fuel','at_allowance','sector_budget','sector_execution']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseFuelBound
namespace Doom.Verification.ExtractedNoiseFuel
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoisePreservation
open E1M1NoiseAccounting E1M1NoiseLedger E1M1NoiseLineProgress E1M1NoiseFuelBound
theorem dispatch_checked (s : X86Memory.State) (safe : DispatchSafe s) :
    (dispatch ⟨s,none,0x26fa8⟩).core.regs 3=s.regs 3 ∧
    (dispatch ⟨s,none,0x26fa8⟩).core.regs 6=s.regs 6 ∧
    (dispatch ⟨s,none,0x26fa8⟩).core.regs 5=s.regs 5 := dispatch_regs s safe
theorem advance_checked (s : X86Control.State)
    (index : (s.core.regs 6).toNat<count s.core) (small : count s.core≤2147483647) :
    remaining (advance s)+1=remaining s := advance_remaining s index small
theorem child_checked (layout : List Word) (s u : X86Control.State) (w : List Word) (n : Nat)
    (child : CheckedTrace layout .sector (dispatch s) u w n) (regs : DispatchSafe s.core)
    (frame : E1M1NoisePreservation.SectorSafe (dispatch s).core w)
    (safe : ∀ b, b ∈ E1M1NoiseFootprint.lineWrites s.core++w → BlockSummary.Apart (s.core.regs 3+(78#32)) b)
    (index : (s.core.regs 6).toNat<count s.core) (small : count s.core≤2147483647) :
    remaining (advance u)+1=remaining s := E1M1NoiseLineProgress.child_remaining child regs frame safe index small
theorem budget_checked (limit : Nat) (layout : List Word) (s t : X86Control.State) (w : List Word) (n : Nat)
    (h : CheckedTrace layout .sector s t w n) (loops : LoopGuards limit h)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout)
    (rep : Represents generation s.core.memory xs) :
    eval (2*layout.length*(limit+1)+1) .sector s=some t := sector_budget h loops generation xs shape rep
theorem execution_checked (limit : Nat) (layout : List Word) (s t : X86Control.State) (w : List Word) (n : Nat)
    (h : CheckedTrace layout .sector s t w n) (loops : LoopGuards limit h)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout)
    (rep : Represents generation s.core.memory xs) (pc : s.pc=0x26f60) :
    Runs (bound (2*layout.length*(limit+1)+1)) s t := sector_execution h loops generation xs shape rep pc
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseFuel\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseFuel.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-fuel';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-accounting')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseFuelBound'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-accounting/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Original opening/dispatch register preservation and exact remaining-line progress under explicit separation and signed-index bounds. Guarded finite recursive traces have fuel at most 2*N*(L+1)+1. Finite traces and their guards are still premises; unconditional termination, reachable-state invariants and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original line progress and explicit guarded traversal fuel bound.')
if __name__=='__main__':main()

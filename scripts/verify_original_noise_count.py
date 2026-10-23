#!/usr/bin/env python3
"""Verify incoming, child and resumed-parent sound-block counts in recursive traversal."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['entry_checked', 'call_checked', 'resume_checked', 'trace_checked', 'budget_checked']
NAMES+=['Doom.Proofs.E1M1NoiseCount.'+n for n in ['start_count', 'advance_count', 'block_child', 'dispatch_count', 'dispatch_child', 'resume_count', 'all_entries', 'sector_budget']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseCount
namespace Doom.Verification.ExtractedNoiseCount
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation E1M1NoiseStack
open E1M1NoiseAccounting E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive E1M1NoiseGraph E1M1NoiseGraphAllocation E1M1NoiseCount

theorem entry_checked (s : X86Control.State) : (startLines s).core.regs 1=s.core.regs 2 := start_count s

theorem call_checked (s : X86Memory.State) (safe : E1M1NoiseOpeningFrame.CallerSafe s)
    (call : (E1M1NoiseIteration.dispatched s).pc=0x26f60) :
    (E1M1NoiseIteration.dispatched s).core.regs 2=s.regs 1 ∨
    (s.regs 1=0 ∧ (E1M1NoiseIteration.dispatched s).core.regs 2=1) := E1M1NoiseCount.dispatch_child s safe call

theorem resume_checked (table : List SectorLines) (stack : Region) (s u : X86Control.State) (w : List Word) (n : Nat)
    (allocation : Allocation table stack)
    (child : CheckedTrace (layout table) .sector (dispatch s) u w n)
    (reserve : Reserve stack .lines n s) (call : (dispatch s).pc=0x26f60) :
    (advance u).core.regs 1=s.core.regs 1 := resume_count allocation child reserve call

theorem trace_checked (table : List SectorLines) (stack : Region) (phase : Phase)
    (s t : X86Control.State) (w : List Word) (n : Nat) (allocation : Allocation table stack)
    (trace : CheckedTrace (layout table) phase s t w n) (reserve : Reserve stack phase n s)
    (entry : Entry phase s) : Every Entry trace.trace := all_entries allocation trace reserve entry

theorem budget_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (regions : List Region) (s t : X86Control.State) (w : List Word) (n limit : Nat)
    (storage : Storage table stack base edges regions) (allocation : Allocation table stack)
    (trace : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32)
    (bounds : Bounded table limit) (map : MapRep table s.core.memory) (graph : GraphRep base edges s.core.memory)
    (entry : Entry .sector s) :
    Every Entry trace.trace ∧ Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory ∧
    eval (2*table.length*(limit+1)+1) .sector s=some t :=
  E1M1NoiseCount.sector_budget storage allocation trace generation xs shape ledger low high bound limit bounds map graph entry
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseCount\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseCount.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-count';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-graph-allocation')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseCount'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-graph-allocation/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Original prologue copies incoming EDX to parent ECX. Dispatch preserves ECX and passes the same count or the first-blocker 0-to-1 increment to child EDX. Allocation and reserve derive exact parent ECX restoration after child return. A generic Every annotation records legal counts at every sector/line entry of the supplied checked trace, and joins frame/map/graph/fuel. The induction does not consult per-node SectorSafe.count, but CheckedTrace still includes ledger guards and is still an input. Static startup certificates, trace construction, termination and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original count transfer, child-call rule, parent restoration and recursive count invariant.')
if __name__=='__main__':main()

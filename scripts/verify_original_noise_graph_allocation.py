#!/usr/bin/env python3
"""Verify allocation-derived graph protection across recursive noise traversal."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['line_checked','sector_checked','trace_checked','entry_checked','budget_checked']
NAMES+=['Doom.Proofs.E1M1NoiseGraphAllocation.Storage.'+n for n in ['protect_sector','protect_line','protect_trace','preserves_graph','child_entry','sector_budget']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseGraphAllocation
namespace Doom.Verification.ExtractedNoiseGraphAllocation
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation E1M1NoiseStack
open E1M1NoiseAccounting E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive E1M1NoiseGraph E1M1NoiseGraphAllocation

theorem line_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (regions : List Region) (s : X86Memory.State)
    (storage : Storage table stack base edges regions) (room : StackRoom stack s) :
    Protect (graphReads base edges) (E1M1NoiseFootprint.lineWrites s) := storage.protect_line room

theorem sector_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (regions : List Region) (s : X86Memory.State) (storage : Storage table stack base edges regions)
    (allocation : Allocation table stack) (room : StackRoom stack s) (member : s.regs 0∈layout table) :
    Protect (graphReads base edges) (E1M1NoiseFootprint.sectorWrites s) := storage.protect_sector allocation room member

theorem trace_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (regions : List Region) (phase : Phase) (s t : X86Control.State) (w : List Word) (n : Nat)
    (storage : Storage table stack base edges regions) (allocation : Allocation table stack)
    (trace : CheckedTrace (layout table) phase s t w n) (reserve : Reserve stack phase n s) :
    Protect (graphReads base edges) w := storage.protect_trace allocation trace reserve

theorem entry_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (regions : List Region) (sector : SectorLines) (s : X86Control.State) (n : Nat)
    (storage : Storage table stack base edges regions) (allocation : Allocation table stack)
    (reserve : Reserve stack .lines n s)
    (covered : Covered table edges) (closed : Closed table edges) (member : sector∈table)
    (map : MapRep table s.core.memory) (cursor : Cursor sector s.core) (graph : GraphRep base edges s.core.memory)
    (count : s.core.regs 1=0 ∨ s.core.regs 1=1) (call : (dispatch s).pc=0x26f60) :
    E1M1NoiseLedger.SectorSafe (layout table) (dispatch s).core ∧
    GraphRep base edges (dispatch s).core.memory ∧ MapRep table (dispatch s).core.memory :=
  storage.child_entry allocation reserve covered closed member map cursor graph count call

theorem budget_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (regions : List Region) (s t : X86Control.State) (w : List Word) (n limit : Nat)
    (storage : Storage table stack base edges regions) (allocation : Allocation table stack)
    (trace : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32)
    (bounds : Bounded table limit) (map : MapRep table s.core.memory) (graph : GraphRep base edges s.core.memory) :
    Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory ∧
    eval (2*table.length*(limit+1)+1) .sector s=some t :=
  storage.sector_budget allocation trace generation xs shape ledger low high bound limit bounds map graph
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseGraphAllocation\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseGraphAllocation.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-graph-allocation';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-graph')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseGraphAllocation'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-graph/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Static placement of graph words in read-only regions derives graph protection against sector, stack and opening-global writes. Induction transports protection across all checked recursive branches from one entry reserve. Child entry no longer assumes graph-write separation; the joined sector theorem preserves frame, map and graph and supplies evaluator fuel. Static allocation/storage certificates, initial relations, finite CheckedTrace and its ledger guards remain premises. DOS startup specialization, trace construction, unconditional termination and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: allocated graph protection, recursive preservation and joined frame/map/graph/fuel result.')
if __name__=='__main__':main()

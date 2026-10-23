#!/usr/bin/env python3
"""Verify admission-bounded recursive stack protection and derived traversal guards."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['guards_checked','reserve_checked','restoration_checked','budget_checked']
NAMES+=['Doom.Proofs.E1M1NoiseStack.'+n for n in ['WritesBelow.append','WritesBelow.mono','Reserve.room','Reserve.mono','Reserve.start','child_stack','Reserve.child','checked_guards','sector_reserve','sector_guards','sector_budget']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseStack
namespace Doom.Verification.ExtractedNoiseStack
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation E1M1NoiseStack
open E1M1NoiseAccounting E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive

theorem guards_checked (table : List SectorLines) (stack : Region) (phase : Phase)
    (s t : X86Control.State) (w : List Word) (n : Nat)
    (allocation : Allocation table stack) (trace : CheckedTrace (layout table) phase s t w n)
    (reserve : Reserve stack phase n s) :
    MemoryGuards table trace ∧ WritesBelow table (ceiling phase s) w ∧ FrameBound table phase s w :=
  checked_guards allocation trace reserve

theorem reserve_checked (table : List SectorLines) (stack : Region) (s t : X86Control.State) (w : List Word) (n : Nat)
    (trace : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32) :
    Reserve stack .sector n s := sector_reserve trace generation xs shape ledger low high bound

theorem restoration_checked (table : List SectorLines) (stack : Region) (s t : X86Control.State) (w : List Word) (n : Nat)
    (allocation : Allocation table stack) (trace : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32) :
    MemoryGuards table trace ∧ Restored s.core t :=
  sector_guards allocation trace generation xs shape ledger low high bound

theorem budget_checked (table : List SectorLines) (stack : Region) (s t : X86Control.State) (w : List Word) (n limit : Nat)
    (allocation : Allocation table stack) (trace : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32)
    (bounds : Bounded table limit) (map : MapRep table s.core.memory) :
    Restored s.core t ∧ MapRep table t.core.memory ∧ eval (2*table.length*(limit+1)+1) .sector s=some t :=
  E1M1NoiseStack.sector_budget allocation trace generation xs shape ledger low high bound limit bounds map
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseStack\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseStack.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-stack';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-allocation')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseStack'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-allocation/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='A 28-byte-per-admission stack reserve derives all extra MemoryGuards and post-prologue child footprints over an existing finite CheckedTrace. The initial ledger gives a sufficient 56*N+20-byte reserve below entry ESP. Static allocation and entry bounds imply full frame restoration, shared-map preservation and explicit evaluator fuel without separate MemoryGuards or LoopGuards. CheckedTrace and its ledger guards, initial relations and actual startup allocation remain premises; unconditional termination, graph closure and live Lean worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: admission-bounded stack protection, automatic memory guards and joined evaluator budget.')
if __name__=='__main__':main()

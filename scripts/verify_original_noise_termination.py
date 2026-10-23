#!/usr/bin/env python3
"""Verify construction and bounded completion of the original recursive noise traversal."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['call_checked', 'construct_checked', 'reserve_checked', 'total_checked', 'execution_checked']
NAMES+=['Doom.Proofs.E1M1NoiseTermination.'+n for n in ['call_word', 'construct_below', 'construct', 'entry_reserve', 'sector_total', 'sector_execution']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseTermination
namespace Doom.Verification.ExtractedNoiseTermination
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation E1M1NoiseStack
open E1M1NoiseAccounting E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive
open E1M1NoiseGraph E1M1NoiseGraphAllocation E1M1NoiseTermination

theorem call_checked (s : X86Control.State) (call : (dispatch s).pc=0x26f60) :
    load32 (dispatch s).core.memory ((dispatch s).core.regs 4)=(0x27006#32) := call_word s call

theorem construct_checked (table : List SectorLines) (stack : Region) (base : Word)
    (edges : List Edge) (regions : List Region) (limit : Nat) (generation : Word)
    (phase : Phase) (s : X86Control.State) (xs : Ledger)
    (world : World table stack base edges regions limit)
    (ready : Ready table base edges generation phase s xs)
    (reserve : Reserve stack phase (credit xs) s) :
    ∃ t w n, CheckedTrace (layout table) phase s t w n := construct world ready reserve

theorem reserve_checked (table : List SectorLines) (stack : Region) (base : Word)
    (edges : List Edge) (generation : Word) (s : X86Control.State) (xs : Ledger)
    (ready : Ready table base edges generation .sector s xs)
    (low : stack.lo+56*table.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    Reserve stack .sector (credit xs) s := entry_reserve ready low high bound

-- Flatten the public assumptions to make omissions and hidden trace premises
-- reviewable. Neither finite execution nor a child postcondition is assumed.
theorem total_checked (table : List SectorLines) (stack : Region) (base : Word)
    (edges : List Edge) (regions : List Region) (limit : Nat) (generation : Word)
    (s : X86Control.State) (xs : Ledger)
    (allocation : Allocation table stack) (storage : Storage table stack base edges regions)
    (bounds : Bounded table limit) (covered : Covered table edges) (closed : Closed table edges)
    (shape : addresses xs=layout table) (ledger : Represents generation s.core.memory xs)
    (map : MapRep table s.core.memory) (graph : GraphRep base edges s.core.memory)
    (member : s.core.regs 0∈layout table) (count : s.core.regs 2=0 ∨ s.core.regs 2=1)
    (low : stack.lo+56*table.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    ∃ t, eval (2*table.length*(limit+1)+1) .sector s=some t ∧
      Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory :=
  sector_total ⟨allocation,storage,bounds,covered,closed⟩
    ⟨shape,ledger,map,graph,member,count⟩ low high bound

theorem execution_checked (table : List SectorLines) (stack : Region) (base : Word)
    (edges : List Edge) (regions : List Region) (limit : Nat) (generation : Word)
    (s : X86Control.State) (xs : Ledger)
    (world : World table stack base edges regions limit)
    (ready : Ready table base edges generation .sector s xs)
    (low : stack.lo+56*table.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) (pc : s.pc=0x26f60) :
    ∃ t, Runs (E1M1NoiseRecursive.bound (2*table.length*(limit+1)+1)) s t ∧
      Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory :=
  sector_execution world ready low high bound pc
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseTermination\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseTermination.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-termination';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-count')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseTermination'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-count/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Constructs a finite CheckedTrace from static allocation/storage/bounds/coverage/closure and entry map/graph/ledger/position/count relations, using ledger credit and remaining-line descent. No finite trace, successful eval, or child return is a premise. Map-sized stack reserve and evaluator fuel yield termination with caller restoration and map/graph preservation, linked to pinned original instruction execution. This is conditional on the stated entry/storage certificates, not their establishment from DOS startup. Live Lean sound-worklist correspondence and whole-game correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: finite trace construction, map-sized completion and original-instruction execution without a trace premise.')
if __name__=='__main__':main()

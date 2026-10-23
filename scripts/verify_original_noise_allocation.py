#!/usr/bin/env python3
"""Verify allocation-derived DOS noise traversal memory protection."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['map_checked','ledger_checked','dispatch_checked','frame_checked','restore_checked']
NAMES+=['Doom.Proofs.E1M1NoiseAllocation.'+n for n in ['Region.Disjoint.symm','Region.apart','sector_contains','array_contains','globals_contains','Allocation.map_sector','Allocation.map_line','Allocation.dispatch_safe','stack_room','Allocation.ledger_sector','Allocation.ledger_line','Allocation.frame_safe','Allocation.restores','Allocation.skip_step','Allocation.child_step']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseAllocation
namespace Doom.Verification.ExtractedNoiseAllocation
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation
open E1M1NoiseAccounting E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseFootprint

theorem map_checked (table : List SectorLines) (stack : Region) (s : X86Memory.State)
    (allocation : Allocation table stack) (room : StackRoom stack s) (member : s.regs 0∈layout table) :
    Protect (mapReads table) (sectorWrites s) := allocation.map_sector room member

theorem ledger_checked (table : List SectorLines) (stack : Region) (s : X86Memory.State)
    (allocation : Allocation table stack) (room : StackRoom stack s) (member : s.regs 0∈layout table)
    (count : s.regs 2=(0#32) ∨ s.regs 2=(1#32)) : E1M1NoiseLedger.SectorSafe (layout table) s :=
  allocation.ledger_sector room member count

theorem dispatch_checked (table : List SectorLines) (stack : Region) (s : X86Memory.State)
    (allocation : Allocation table stack) (room : StackRoom stack s) : E1M1NoiseLineProgress.DispatchSafe s :=
  allocation.dispatch_safe room

theorem frame_checked (table : List SectorLines) (stack : Region) (s : X86Memory.State) (w : List Word)
    (allocation : Allocation table stack) (room : StackRoom stack s) (low : 20 ≤ (s.regs 4).toNat)
    (footprint : BelowFrame table s w) : E1M1NoisePreservation.SectorSafe s w :=
  allocation.frame_safe room low footprint

theorem restore_checked (table : List SectorLines) (stack : Region) (s t : X86Control.State) (w : List Word) (n : Nat)
    (allocation : Allocation table stack) (trace : CheckedTrace (layout table) .sector s t w n)
    (room : StackRoom stack s.core) (low : 20 ≤ (s.core.regs 4).toNat)
    (footprint : BelowFrame table s.core w) : Restored s.core t :=
  allocation.restores trace room low footprint
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseAllocation\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseAllocation.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-allocation';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-map')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseAllocation'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-map/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Nonwrapping byte-region allocation derives local map, visit-ledger and helper-register protection. A below-frame footprint derives saved-frame restoration and feeds child-resumption progress. Allocation, stack room, child footprint and checked finite trace remain premises. DOS startup specialization, reachable stack-depth invariants, unconditional termination and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: allocation-derived map, ledger, helper and saved-frame protection.')
if __name__=='__main__':main()

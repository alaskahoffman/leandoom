#!/usr/bin/env python3
"""Verify shared original map invariants and derived recursive loop guards."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['map_checked','selection_checked','branch_checked','guards_checked','budget_checked']
NAMES+=['Doom.Proofs.E1M1NoiseMap.'+n for n in ['entry_mem','Rep.frame','MapRep.frame','MapRep.sector_step','MapRep.dispatch_step','MapRep.traversal','Rep.count_nat','Cursor.selected','Cursor.remaining_eq','Cursor.advance_branch','Cursor.after_advance','Cursor.after_dispatch','Cursor.after_child','start_step','skip_step','child_step']]
NAMES+=['Doom.Proofs.E1M1NoiseMapGuards.'+n for n in ['protect_append','MemoryGuards.protected','MemoryGuards.loops','MemoryGuards.preserves_map','sector_budget']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseMapGuards
namespace Doom.Verification.ExtractedNoiseMap
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoisePreservation E1M1NoiseAccounting
open E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseFuelBound
theorem map_checked (table : List SectorLines) (phase : Phase) (s t : X86Control.State) (w : List Word)
    (rep : MapRep table s.core.memory) (trace : Trace phase s t w) (safe : Protect (mapReads table) w) :
    MapRep table t.core.memory := rep.traversal trace safe
theorem selection_checked (e : SectorLines) (s : X86Memory.State) (cursor : Cursor e s)
    (rep : E1M1NoiseMap.Rep e s.memory) :
    (NoiseTraversal.selected s).regs 2=e.lines[(s.regs 6).toNat]'cursor.live := cursor.selected rep
theorem branch_checked (e : SectorLines) (s : X86Control.State) (cursor : Cursor e s.core)
    (rep : E1M1NoiseMap.Rep e s.core.memory) (small : e.lines.length≤2147483647) :
    (advance s).pc=0x26fa8 ↔ (s.core.regs 6).toNat+1<e.lines.length := cursor.advance_branch rep small
theorem guards_checked (table : List SectorLines) (phase : Phase) (s t : X86Control.State) (w : List Word) (n limit : Nat)
    (h : CheckedTrace (layout table) phase s t w n) (guards : MemoryGuards table h)
    (bounds : Bounded table limit) (rep : MapRep table s.core.memory) (entry : Entry table phase s) :
    LoopGuards limit h := guards.loops limit bounds rep entry
theorem budget_checked (table : List SectorLines) (s t : X86Control.State) (w : List Word) (n limit : Nat)
    (h : CheckedTrace (layout table) .sector s t w n) (guards : MemoryGuards table h)
    (bounds : Bounded table limit) (map : MapRep table s.core.memory) (generation : Word) (xs : Ledger)
    (shape : addresses xs=layout table) (rep : Represents generation s.core.memory xs) :
    eval (2*table.length*(limit+1)+1) .sector s=some t :=
  E1M1NoiseMapGuards.sector_budget h guards limit bounds map generation xs shape rep
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseMap\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseMap.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-map';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-fuel')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseMapGuards'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-fuel/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Shared representation of original sector line counts, pointers and ordered arrays; selection and cursor progress follow from original summaries. Memory separation annotations on finite checked traces derive all numeric loop guards and the explicit fuel bound. Finite traces and physical protection remain premises; fixed E1M1 initialization/all-reachable-state invariants, unconditional termination and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: original map preservation, cursor progress and derived recursive loop guards.')
if __name__=='__main__':main()

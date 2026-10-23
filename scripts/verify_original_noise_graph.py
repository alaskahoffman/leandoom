#!/usr/bin/env python3
"""Verify original signed neighbor lookup and graph-closed recursive child entry."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['opening_checked','neighbor_checked','dispatch_checked','frame_checked','entry_checked']
NAMES+=['Doom.Proofs.E1M1NoiseOpeningFrame.'+n for n in ['restored','opened','allocation_safe','opening_returns']]
NAMES+=['Doom.Proofs.E1M1NoiseFootprint.opened_frame']
NAMES+=['Doom.Proofs.E1M1NoiseGraph.'+n for n in ['load16_of_word','byte_of_word','EdgeRep.frame','GraphRep.frame','GraphRep.sector_step','GraphRep.dispatch_step','GraphRep.traversal','neighbor_choice','neighbor_closed','selected_edge','opening_child','dispatch_child','child_entry']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseGraph
namespace Doom.Verification.ExtractedNoiseGraph
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation E1M1NoiseStack
open E1M1NoiseAccounting E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive E1M1NoiseGraph

theorem opening_checked (table : List SectorLines) (stack : Region) (s : X86Memory.State)
    (allocation : Allocation table stack) (room : StackRoom stack s) : OpeningReturns s :=
  E1M1NoiseOpeningFrame.opening_returns allocation room

theorem neighbor_checked (base : Word) (e : Edge) (s : X86Memory.State)
    (rep : EdgeRep base e s.memory) (global : load32 s.memory (0x2c118#32)=base)
    (selected : s.regs 2=e.line) (two : e.two) (safe : Protect (edgeReads base e) [s.regs 4]) :
    (E1M1NoiseOpening.neighbor s).core.regs 0=if s.regs 3=e.front then e.back else e.front :=
  neighbor_choice rep global selected two safe

theorem dispatch_checked (table : List SectorLines) (base : Word) (edges : List Edge) (sector : SectorLines) (s : X86Memory.State)
    (covered : Covered table edges) (closed : Closed table edges) (member : sector∈table)
    (map : E1M1NoiseMap.Rep sector s.memory) (cursor : Cursor sector s) (graph : GraphRep base edges s.memory)
    (safe : Protect (graphReads base edges) (E1M1NoiseFootprint.lineWrites s))
    (saved : E1M1NoiseOpeningFrame.CallerSafe s) (count : s.regs 1=0 ∨ s.regs 1=1)
    (call : (E1M1NoiseIteration.dispatched s).pc=0x26f60) :
    (E1M1NoiseIteration.dispatched s).core.regs 0∈layout table ∧
    ((E1M1NoiseIteration.dispatched s).core.regs 2=0 ∨ (E1M1NoiseIteration.dispatched s).core.regs 2=1) :=
  dispatch_child covered closed member map cursor graph safe saved count call

theorem frame_checked (base : Word) (edges : List Edge) (phase : Phase) (s t : X86Control.State) (w : List Word)
    (rep : GraphRep base edges s.core.memory) (trace : Trace phase s t w)
    (safe : Protect (graphReads base edges) w) : GraphRep base edges t.core.memory :=
  rep.traversal trace safe

theorem entry_checked (table : List SectorLines) (stack : Region) (base : Word) (edges : List Edge)
    (sector : SectorLines) (s : X86Control.State) (n : Nat)
    (allocation : Allocation table stack) (reserve : Reserve stack .lines n s)
    (covered : Covered table edges) (closed : Closed table edges) (member : sector∈table)
    (map : MapRep table s.core.memory) (cursor : Cursor sector s.core) (graph : GraphRep base edges s.core.memory)
    (safe : Protect (graphReads base edges) (E1M1NoiseFootprint.lineWrites s.core))
    (count : s.core.regs 1=0 ∨ s.core.regs 1=1) (call : (dispatch s).pc=0x26f60) :
    E1M1NoiseLedger.SectorSafe (layout table) (dispatch s).core ∧
    GraphRep base edges (dispatch s).core.memory ∧ MapRep table (dispatch s).core.memory :=
  child_entry allocation reserve covered closed member map cursor graph safe count call
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseGraph\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseGraph.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-graph';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-stack')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseGraph'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-stack/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='Opening helper preserves selected line and incoming count and returns to its actual CALL site under allocation-derived protection. A shared signed-side-table representation proves exact original neighbor selection and preservation under protected writes. Covered/closed graph data derive child membership and the legal incoming count through complete dispatch, then join the existing checked child-entry contract. Initial graph/map relations, static coverage/closure, graph-word protection and entry count remain premises; allocation of graph words, trace construction, unconditional termination and live worklist correspondence remain open.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: opening return, exact signed neighbor selection, graph preservation and checked child entry.')
if __name__=='__main__':main()

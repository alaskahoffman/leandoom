#!/usr/bin/env python3
"""Verify sparse byte initialization of sound traversal map, graph and fresh ledger."""
import json,re,subprocess
import verify_original_noise_recursive as recursive
ROOT,require=recursive.ROOT,recursive.require
NAMES=['word_checked', 'patch_checked', 'initialized_checked', 'completion_checked']
NAMES+=['Doom.Proofs.E1M1NoiseImage.'+n for n in ['realizes', 'frame', 'read_half', 'read_word', 'apply_word', 'map_rep', 'graph_rep', 'initializes', 'fresh_shape', 'fresh_rep', 'initializes_fresh', 'completes']]
def certificate():
    s='''import Doom.Proofs.E1M1NoiseImage
namespace Doom.Verification.ExtractedNoiseImage
open Doom Doom.Proofs X86 X86Memory X86Control E1M1NoiseAllocation E1M1NoisePreservation
open E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger E1M1NoiseRecursive
open E1M1NoiseGraph E1M1NoiseGraphAllocation E1M1NoiseTopology E1M1NoiseImage

theorem word_checked (m : Memory) (a v : Word) : applyPatch (word a v) m=store32 m a v := apply_word m a v

theorem patch_checked (p : E1M1NoiseImage.Patch) (m : Memory) (consistent : Consistent p) :
    Realizes p (applyPatch p m) := realizes consistent m

theorem initialized_checked (table : List SectorLines) (base : Word) (edges : List Edge)
    (generation old : Word) (different : old≠generation)
    (consistent : Consistent (freshImage table base edges generation old)) (before : Memory) :
    MapRep table (applyPatch (freshImage table base edges generation old) before) ∧
    GraphRep base edges (applyPatch (freshImage table base edges generation old) before) ∧
    Represents generation (applyPatch (freshImage table base edges generation old) before) (freshLedger table) :=
  initializes_fresh table base edges generation old different consistent before

theorem completion_checked (t : Topology) (limit : Nat) (stack : Region) (base : Word) (regions : List Region)
    (generation old : Word) (s : X86Control.State) (h : Certified t limit) (a : Addresses)
    (allocation : Allocation (t.table a) stack) (storage : Storage (t.table a) stack base (t.edges a) regions)
    (different : old≠generation) (consistent : Consistent (freshImage (t.table a) base (t.edges a) generation old))
    (index : Nat) (inside : index<t.sectors.length) (sector : s.core.regs 0=a.sector index)
    (count : s.core.regs 2=0 ∨ s.core.regs 2=1)
    (low : stack.lo+56*t.sectors.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    ∃ out, eval (2*t.sectors.length*(limit+1)+1) .sector
        (initialized (t.table a) base (t.edges a) generation old s)=some out ∧
      Restored (initialized (t.table a) base (t.edges a) generation old s).core out ∧
      MapRep (t.table a) out.core.memory ∧ GraphRep base (t.edges a) out.core.memory :=
  E1M1NoiseImage.completes h a allocation storage different consistent index inside sector count low high bound
'''
    return s+'\n'.join('#print axioms '+n for n in NAMES)+'\nend Doom.Verification.ExtractedNoiseImage\n'
def audit(output):
    rest=output.strip()
    for short in NAMES:
        name=short if '.' in short else 'Doom.Verification.ExtractedNoiseImage.'+short
        m=re.match(re.escape(f"'{name}'")+r'\s+(?:depends on axioms: \[([^\[\]]*)\]|does not depend on any axioms)',rest)
        require(m is not None,'missing audit: '+name)
        axioms={a.strip() for a in (m[1] or '').split(',') if a.strip()}
        require(axioms<={'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+str(axioms));rest=rest[m.end():].strip()
    require(not rest,'unexpected certificate output')
def main():
    out=ROOT/'artifacts/original-noise-image';out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').unlink(missing_ok=True)
    with (out/'dependencies.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/verify-original-noise-topology')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    with (out/'build.log').open('w') as log:
        subprocess.run([str(ROOT/'scripts/lake'),'build','Doom.Proofs.E1M1NoiseImage'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    path=out/'Checked.lean';path.write_text(certificate())
    r=subprocess.run([str(ROOT/'scripts/lake'),'env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
    if r.returncode:print(r.stdout);print(r.stderr);r.check_returncode()
    audit(r.stdout);require(not r.stderr.strip(),'unexpected stderr')
    dep=json.loads((ROOT/'artifacts/original-noise-topology/report.json').read_text())
    (out/'report.json').write_text(json.dumps(dict(exe_sha256=dep['exe_sha256'],audited_declarations=len(NAMES),
        axioms=r.stdout.splitlines(),scope='A consistent sparse byte-write plan on arbitrary prior memory establishes the original MapRep, GraphRep and fresh visitation ledger. Repeated shared writes must agree; untouched bytes are preserved. Word emission equals x86 store32 even for wrapping/unaligned addresses. Completion is proved for the initialized entry without assuming output memory relations. This initializer specifies relevant field writes; it is not a proof of DOS loader instruction execution or runtime startup. Physical Allocation/Storage, write consistency, fresh generation and register/stack entry conditions remain explicit. Caller restoration refers to initialized entry memory; pre-initialization return-word preservation is a separate obligation.'),indent=2)+'\n')
    print(r.stdout,end='');print('PASS: sparse initializer derives map, graph and fresh ledger and connects to bounded completion.')
if __name__=='__main__':main()

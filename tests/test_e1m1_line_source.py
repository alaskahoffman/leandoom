"""DOS scan/source-loop contracts retain order, history, capacity and validation."""
import re
import unittest
from pathlib import Path
import test_e1m1_mixed_cell_walk as prior
import verify_e1m1_line_source as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1LineSourceScan
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineMixedInvariant (Candidate Initial Stable)
open OriginalLineVisits (Represents markPrefix)
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
attribute [local irreducible] load32
'''
SCAN='s sp cursor lines objects trace c data stack list items ids ready layout stamps f r tracked epoch seen size represented sceneLines lookup'
FIXTURE=HEADER+'''
open E1M1LineSourceLoop
def trace : Collision.Divline := ⟨⟨0⟩,⟨0⟩,⟨4194304⟩,⟨0⟩⟩
def wall (x : Int32) : Collision.Line :=
  { x:=⟨x⟩, y:=⟨-65536⟩, dx:=⟨0⟩, dy:=⟨131072⟩,
    bbox:=default, slope:=.vertical, front:=default }
def r : Collision.PathResult := {trace:=trace}
'''

class LineSourceTests(unittest.TestCase):
    lean=prior.MixedCellWalkTests.lean
    succeeds=prior.MixedCellWalkTests.succeeds
    rejects=prior.MixedCellWalkTests.rejects
    mutations=prior.MixedCellWalkTests.mutations

    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        context=''
        if module=='E1M1LineSourceScan' and name!='candidate_ids':
            context=source[source.index('variable (',source.index('section Scan')):source.index('/-- The actual DOS')]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('LineCollect.visit_step','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_callback_needs_flags_and_live_stamp_representation(self):
        self.mutations(self.contract('E1M1LineCollect','visit_step','initial n base lines resolve h count layout i s r inv hi flags epoch seen size represented'),[
            ('(flags : (h.candidates i).flags=3)','(flags : True)'),
            ('(represented : Represents s.core.memory lines epoch seen)','(represented : True)'),
            ('(inv : Stable initial h i s r)','(inv : True)')])

    def test_scan_retains_budget_and_marks_rejected_lines(self):
        self.mutations(self.contract('E1M1LineCollect','collect_run','initial n base lines resolve h count layout i s r inv k bound flags epoch seen size represented'),[
            ('(bound : i+k≤n)','(bound : True)'),
            ('markPrefix h.candidates k i seen','seen')])

    def test_source_loop_requires_correct_trace_lookup_and_signed_ids(self):
        self.mutations(self.contract('E1M1LineSourceLoop','source_collect','trace lines cs seen r traces ids lookup'),[
            ('(traces : ∀ c∈cs, c.trace=trace)','(traces : True)'),
            ('(ids : ∀ c∈cs, c.id<32768)','(ids : True)'),
            ('(lookup : ∀ c∈cs, lines[c.id]?=some c.line)','(lookup : True)')])

    def test_machine_join_needs_initial_capacity_and_source_scene(self):
        self.mutations(self.contract('E1M1LineSourceScan','execution',SCAN),[
            ('(tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)','(tracked : True)'),
            ('(lookup : ∀ i : Fin c.ids.length, sceneLines[c.ids[i.val]]?=some (data i.val).line)','(lookup : True)'),
            ('⟨s,f,0x2c57f⟩ out.1','⟨s,f,0x2c580⟩ out.1')])

    def test_duplicate_lines_append_once_in_raw_order(self):
        self.succeeds(FIXTURE+'''
-- Farther wall first: the collector must not sort by fraction.
example : ((lineCell trace #[wall 2097152,wall 1048576] #[0,1,0]
    #[false,false] r).toOption.map (fun out =>
      (out.1.toList, out.2.collected.toList.map (fun hit => (hit.id,hit.frac.raw))))) =
    some ([true,true], [(0,32768),(1,16384)]) := by decide +kernel
''')

    def test_guard_and_lookup_precede_duplicate_skip(self):
        self.succeeds(FIXTURE+'''
example : lineCell trace #[] #[0] #[true] r =
    .error "path: invalid linedef" := by rfl
example : lineCell trace #[] #[32768] #[] r =
    .error "path: signed linedef index is unverified" := by rfl
''')

    def test_rejection_marks_seen_and_capacity_is_not_reset(self):
        self.succeeds(FIXTURE+'''
def miss : Collision.Line := { wall 1048576 with y:=⟨65536⟩ }
example : (lineCell trace #[miss] #[0,0] #[false] r).map
    (fun out => (out.1,out.2.collected.size)) = .ok (#[true],0) := by rfl
-- A pre-existing full mixed collection cannot be cleared to make room.
def full : Collision.PathResult := { r with collected:=Array.replicate 128 ⟨⟨1⟩,false,7⟩ }
example : lineCell trace #[wall 1048576] #[0] #[false] full =
    .error "path: intercept overflow profile is unverified" := by rfl
example : (lineCell trace #[wall 1048576] #[0] #[true] full).map
    (fun out => out.2.collected.size) = .ok 128 := by rfl
''')

if __name__=='__main__':unittest.main()

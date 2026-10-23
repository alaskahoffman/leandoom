"""Logged cell replay keeps source scene relations, history and the shared budget."""
import re
import unittest
from pathlib import Path
import test_e1m1_traversal_source as prior
import test_e1m1_line_source as fixtures
import verify_e1m1_logged_walk as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='''import Doom.Proofs.E1M1LoggedWalk
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State Static caller_safe)
open E1M1CellWalk (Follows grid stopPc)
open E1M1MixedCellWalk (inside Admitted Images cost instructions budget bound visits history)
open E1M1CollectionLog (log state_log)
attribute [local irreducible] load32 E1M1LoggedCell.next E1M1LoggedCell.collect
'''
WALK='q cells s r seen common height statics scenes state images entry follows room'
FIXTURE=fixtures.FIXTURE.replace('import Doom.Proofs.E1M1LineSourceScan','import Doom.Proofs.E1M1LoggedWalk')+'''
def world : Collision.Scene :=
  { grid:={origin:=⟨0,0⟩,width:=1,height:=1,cells:=#[#[]]},
    lines:=#[wall 1048576],links:=#[#[]] }
def cell (x y : Int32) : E1M1CellWalkInvariant.Cell :=
  ⟨x,y,⟨0,[]⟩,(fun _ => ⟨wall 1048576,0,0,⟨0⟩⟩),[]⟩
'''

class LoggedWalkTests(unittest.TestCase):
    lean=prior.TraversalSourceTests.lean
    succeeds=prior.TraversalSourceTests.succeeds
    rejects=prior.TraversalSourceTests.rejects
    mutations=prior.TraversalSourceTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',s[a:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('CellLineSource.lines','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_line_source_is_derived_from_the_real_gate_and_scene(self):
        # This theorem uses the in-map Images relation, not the mixed relation.
        source=self.contract('E1M1CellLineSource','lines','q c s r seen common static state images pc x y room scene')
        source=source.replace('Admitted Images cost','Admitted cost')
        source=source.replace('namespace Doom.Proofs.E1M1CellLineSource','open E1M1CellWalkInvariant (Images)\nnamespace Doom.Proofs.E1M1CellLineSource',1)
        self.mutations(source,[('(scene : SceneLines q c)','(scene : True)'),
            ('(pc : s.pc=0x2ca7f)','(pc : True)'),
            ('(images : Images q [c] s.core.memory)','(images : True)')])

    def test_cell_needs_matching_height_and_in_map_scene_data(self):
        self.mutations(self.contract('E1M1LoggedCell','one','q c s r seen common height static scene state images pc x y room'),[
            ('(height : q.world.grid.height=q.height)','(height : True)'),
            ('(scene : inside q c=true → E1M1CellLineSource.SceneLines q c)','(scene : True)')])

    def test_walk_needs_one_budget_and_retains_history(self):
        self.mutations(self.contract('E1M1LoggedWalk','execution',WALK),[
            ('(room : r.collected.size+budget q cells≤128)','(room : r.collected.size≤128)'),
            ('State q out after (history q seen cells)','State q out after seen'),
            ('collect q.trace q.world cells seen r=.ok (history q seen cells,after)',
             'collect q.trace q.world cells seen r=.ok (seen,after)')])

    def test_walk_requires_initial_images_and_the_actual_numeric_route(self):
        self.mutations(self.contract('E1M1LoggedWalk','execution',WALK),[
            ('(images : Images q cells s.core.memory)','(images : True)'),
            ('(follows : Follows (E1M1PathAdvance.observe s.core) cells)','(follows : True)'),
            ('(scenes : ∀ c∈cells, inside q c=true → E1M1CellLineSource.SceneLines q c)','(scenes : True)')])

    def test_outside_cells_log_both_visits_without_array_lookups(self):
        self.succeeds(FIXTURE+'''
example : (E1M1LoggedCell.collect trace { world with lines:=#[],links:=#[] }
    (-1) 0 #[] r).toOption.map (fun out => (out.1.toList,out.2.blocks.toList,out.2.collected.size)) =
    some ([],[(true,-1,0),(false,-1,0)],0) := by decide +kernel
''')

    def test_repeated_cells_log_again_but_keep_line_deduplication(self):
        self.succeeds(FIXTURE+'''
example : (E1M1LoggedWalk.collect trace world [cell 0 0,cell 0 0] #[false] r).toOption.map
    (fun out => (out.1.toList,out.2.blocks.toList,out.2.collected.toList.map (fun hit => hit.id))) =
    some ([true],[(true,0,0),(false,0,0),(true,0,0),(false,0,0)],[0]) := by decide +kernel
''')

    def test_logging_does_not_hide_capacity_errors_or_reset_old_hits(self):
        self.succeeds(FIXTURE+'''
def full : Collision.PathResult := { r with collected:=Array.replicate 128 ⟨⟨1⟩,false,7⟩ }
example : E1M1LoggedCell.collect trace world 0 0 #[false] full =
    .error "path: intercept overflow profile is unverified" := by rfl
example : (E1M1LoggedCell.collect trace world 0 0 #[true] full).toOption.map
    (fun out => (out.2.collected.size,out.2.blocks.toList)) =
    some (128,[(true,0,0),(false,0,0)]) := by decide +kernel
''')

if __name__=='__main__':unittest.main()

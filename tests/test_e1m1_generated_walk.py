"""Numeric itineraries must preserve exact stopping, wrapping and machine contracts."""
import re
import unittest
from pathlib import Path
import test_e1m1_logged_walk as prior
import verify_e1m1_generated_walk as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1LoggedWalk','import Doom.Proofs.E1M1GeneratedWalk')
HEADER+='open E1M1GridRoute (route sourceRoute selected)\n'
FIXTURE=prior.FIXTURE.replace('import Doom.Proofs.E1M1LoggedWalk','import Doom.Proofs.E1M1GeneratedWalk')+'''
open E1M1GridRoute
-- Both axis guards fail; the route repeats until its counter expires.
def stalled : E1M1PathAdvance.Cell :=
  ⟨0,0,8,8,65536,65536,1,1,65536,65536,0⟩
def coords (cs : List E1M1CellWalkInvariant.Cell) := cs.map (fun c => (c.x,c.y))
'''
EXECUTION='q pick s r seen n legal counter common height statics scenes state images entry room'

class GeneratedWalkTests(unittest.TestCase):
    lean=prior.LoggedWalkTests.lean
    succeeds=prior.LoggedWalkTests.succeeds
    rejects=prior.LoggedWalkTests.rejects
    mutations=prior.LoggedWalkTests.mutations

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
                    out+'extra',out.replace('GridRoute.follows','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_exit_requires_legal_counter_and_exact_remaining_budget(self):
        self.mutations(self.contract('E1M1GridRoute','exits','pick fuel n pc g legal remaining counter'),[
            ('(legal : n<64)','(legal : True)'),
            ('(remaining : fuel=64-n)','(remaining : True)'),
            ('(counter : g.count=BitVec.ofNat 32 n)','(counter : True)'),
            ('stopPc pc g (route pick fuel g)=0x2cafd','stopPc pc g (route pick fuel g)=0x2ca7f')])

    def test_generated_execution_still_requires_initial_images_and_capacity(self):
        self.mutations(self.contract('E1M1GeneratedWalk','execution',EXECUTION),[
            ('(images : Images q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)) s.core.memory)',
             '(images : True)'),
            ('(room : r.collected.size+budget q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core))≤128)',
             '(room : r.collected.size≤128)'),
            ('(entry : s.pc=0x2ca7f)','(entry : True)')])

    def test_generated_execution_retains_scene_relation_and_log_history(self):
        self.mutations(self.contract('E1M1GeneratedWalk','execution',EXECUTION),[
            ('(scenes : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core),\n      inside q c=true → E1M1CellLineSource.SceneLines q c)',
             '(scenes : True)'),
            ('State q out after (history q seen cells)','State q out after seen'),
            ('out.pc=0x2cafd','out.pc=0x2ca7f')])

    def test_stall_collects_exactly_64_cells_then_exits(self):
        self.succeeds(FIXTURE+'''
example : (route cell 64 stalled).length=64 := by decide +kernel
example : coords (route cell 64 stalled)=List.replicate 64 (0,0) := by decide +kernel
example : (E1M1CellWalk.grid stalled (route cell 64 stalled)).count=64 := by decide +kernel
example : E1M1CellWalk.stopPc 0x2ca7f stalled (route cell 64 stalled)=0x2cafd := by decide +kernel
''')

    def test_endpoint_collects_current_cell_before_stopping(self):
        self.succeeds(FIXTURE+'''
def endpoint := { stalled with endX:=0,endY:=0 }
example : coords (route cell 64 endpoint)=[(0,0)] := by decide +kernel
example : E1M1CellWalk.grid endpoint (route cell 64 endpoint)=endpoint := by decide +kernel
example : coords (route cell 64 {endpoint with count:=63})=[(0,0)] := by decide +kernel
''')

    def test_axis_priority_and_endpoint_inclusion(self):
        self.succeeds(FIXTURE+'''
-- Both axis guards match initially: the X step wins.
def both := { stalled with xi:=0,yi:=0,endX:=1,endY:=0 }
example : coords (route cell 64 both)=[(0,0),(1,0)] := by decide +kernel
def diagonal := { stalled with xi:=65536,yi:=0,endX:=1,endY:=1 }
example : coords (route cell 64 diagonal)=[(0,0),(1,0),(1,1)] := by decide +kernel
example : coords (sourceRoute cell 64 diagonal)=[(0,0),(1,0),(1,1)] := by decide +kernel
''')

    def test_metadata_cannot_steer_route_or_hide_signed_coordinate_wrap(self):
        self.succeeds(FIXTURE+'''
def unrelated (_ _ : Int32) := cell 123 456
def wrapping := { stalled with mapX:=2147483647,mapY:=0,yi:=0,endX:=2147483648,endY:=0 }
example : coords (route unrelated 64 wrapping)=[(2147483647,0),(-2147483648,0)] := by decide +kernel
''')

    def test_resume_counter_and_unmatched_budget_are_not_silently_ignored(self):
        self.succeeds(FIXTURE+'''
example : (route cell 64 {stalled with count:=63}).length=1 := by decide +kernel
example : (sourceRoute cell 1 {stalled with count:=63}).length=1 := by decide +kernel
-- These differ when the source budget disagrees with the machine counter.
example : (sourceRoute cell 64 {stalled with count:=63}).length=64 := by decide +kernel
example : E1M1CellWalk.stopPc 0x2ca7f stalled (route cell 1 stalled)=0x2ca7f := by decide +kernel
''')

if __name__=='__main__':unittest.main()

"""The generated route must describe the live loop, retaining its control and errors."""
import re
import unittest
from pathlib import Path
import test_e1m1_generated_walk as prior
import verify_e1m1_live_walk as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1GeneratedWalk','import Doom.Proofs.E1M1LiveWalk')
FIXTURE=prior.FIXTURE.replace('import Doom.Proofs.E1M1GeneratedWalk','import Doom.Proofs.E1M1LiveWalk')+'''
open E1M1LiveWalk
'''

class LiveWalkTests(unittest.TestCase):
    lean=prior.GeneratedWalkTests.lean
    succeeds=prior.GeneratedWalkTests.succeeds
    rejects=prior.GeneratedWalkTests.rejects
    mutations=prior.GeneratedWalkTests.mutations

    def contract(self,module,name,args):
        s=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        a=re.search(r'^theorem '+name+r'(?: | :)',s,re.M).start()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',s[a:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def extraction(self):
        s=(ROOT/'Doom/Proofs/E1M1TraversalLoop.lean').read_text()
        return s.replace('namespace Doom.Proofs.E1M1TraversalLoop','namespace Doom.Proofs.ScratchLiveLoop').replace('end Doom.Proofs.E1M1TraversalLoop','end Doom.Proofs.ScratchLiveLoop')

    def control_extraction(self):
        s='import Doom.Proofs.E1M1LiveWalk\n'+self.extraction().split('/-- One iteration')[0]
        return s+'''
attribute [local irreducible] ForIn.forIn Bind.bind
example (ex ey dx dy : Int32) (xs ys yi xi : Fixed) (r : PathResult)
    (x y : Int32) (seen : Array Bool) :
    finish ex ey dx dy xs ys r yi xi x y seen =
      E1M1TraversalLoop.finish ex ey dx dy xs ys r yi xi x y seen := by rfl
example (scene : Scene) (trace : Divline) (ids : Array Nat) (r : PathResult) :
    objectLoop scene trace ids r=E1M1TraversalLoop.objectLoop scene trace ids r := by rfl
end Doom.Proofs.ScratchLiveLoop
'''

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('TraversalLoop.live','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_live_extraction_rejects_budget_raw_list_and_log_drift(self):
        self.mutations(self.extraction(),[
            ('forIn [:fuel]','forIn [:fuel+1]'),
            ('(#[0] ++ ids)','ids'),
            ('blocks.push (true,x,y)','blocks.push (false,x,y)')])

    def test_live_extraction_rejects_endpoint_axis_and_error_drift(self):
        self.mutations(self.control_extraction(),[
            ('x==ex && y==ey','x==ex || y==ey'),
            ('yi.raw >>> 16==y','yi.raw >>> 16==x'),
            ('path: invalid actor link','path: missing actor link')])

    def test_live_extraction_retains_post_loop_order_and_visitor(self):
        self.mutations(self.extraction(),[
            ('work[i]!.frac.raw < distance','work[i]!.frac.raw ≤ distance'),
            ('if !visit hit (result.visited.size - 1)','if visit hit (result.visited.size - 1)')])

    def test_live_dos_join_still_needs_memory_and_capacity(self):
        self.mutations(self.contract('E1M1LiveWalk','execution',prior.EXECUTION),[
            ('(images : Images q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)) s.core.memory)',
             '(images : True)'),
            ('(room : r.collected.size+budget q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core))≤128)',
             '(room : r.collected.size≤128)'),
            ('(entry : s.pc=0x2ca7f)','(entry : True)')])

    def test_live_dos_join_retains_final_numeric_state_and_history(self):
        self.mutations(self.contract('E1M1LiveWalk','execution',prior.EXECUTION),[
            ('E1M1LoopReplay.pack (E1M1PathAdvance.observe out.core)','E1M1LoopReplay.pack (E1M1PathAdvance.observe s.core)'),
            ('State q out after (history q seen cells)','State q out after seen'),
            ('out.pc=0x2cafd','out.pc=0x2ca7f')])

    def test_actual_loop_stalls_to_budget_and_keeps_outside_logs(self):
        self.succeeds(FIXTURE+'''
def outside := {stalled with mapX:=4294967295}
example : (source world trace 64 outside #[false] r).toOption.map
    (fun s => (s.1.isNone,s.2.1.blocks.size,s.2.1.collected.size,s.2.2.2.2.2.2.toList)) =
    some (true,128,0,[false]) := by decide +kernel
example : (source world trace 0 outside #[false] r).toOption.map
    (fun s => (s.2.1.blocks.size,s.2.2.2.2.2.2.toList)) = some (0,[false]) := by decide +kernel
''')

    def test_actual_loop_collects_endpoint_before_stopping_and_deduplicates(self):
        self.succeeds(FIXTURE+'''
def endpoint := {stalled with endX:=0,endY:=0}
example : (source world trace 64 endpoint #[false] r).toOption.map
    (fun s => (s.1.isNone,s.2.1.blocks.toList,s.2.1.collected.size,s.2.2.2.2.2.2.toList)) =
    some (true,[(true,0,0),(false,0,0)],1,[true]) := by decide +kernel
example : (source world trace 3 stalled #[false] r).toOption.map
    (fun s => (s.2.1.blocks.size,s.2.1.collected.size,s.2.2.2.2.2.2.toList)) =
    some (6,1,[true]) := by decide +kernel
''')

    def test_actual_loop_preserves_errors_even_at_endpoint(self):
        self.succeeds(FIXTURE+'''
def endpoint := {stalled with endX:=0,endY:=0}
def errorOf {α : Type} (v : Except String α) : Option String :=
  match v with | .error e => some e | .ok _ => none
example : errorOf (source {world with lines:=#[]} trace 64 endpoint #[true] r) =
    some "path: invalid linedef" := by decide +kernel
example : errorOf (source {world with links:=#[]} trace 64 endpoint #[true] r) =
    some "path: missing thing cell" := by decide +kernel
''')

    def test_actual_loop_keeps_signed_wrap_and_first_axis_priority(self):
        self.succeeds(FIXTURE+'''
def wrapping := {stalled with mapX:=2147483647,yi:=0,endX:=2147483648,endY:=0}
example : (source world trace 64 wrapping #[] r).toOption.map
    (fun s => (s.2.2.2.2.1,s.2.2.2.2.2.1,s.2.1.blocks.toList)) =
    some (-2147483648,0,[(true,2147483647,0),(false,2147483647,0),
      (true,-2147483648,0),(false,-2147483648,0)]) := by decide +kernel
-- Both axis guards match: X wins and the next iteration collects the endpoint.
def both := {stalled with xi:=0,yi:=0,endX:=1,endY:=0}
example : (source world trace 64 both #[false] r).toOption.map
    (fun s => (s.2.2.2.2.1,s.2.2.2.2.2.1,s.2.1.blocks.size)) = some (1,0,4) := by decide +kernel
''')

if __name__=='__main__':unittest.main()

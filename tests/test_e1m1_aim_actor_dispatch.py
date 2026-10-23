"""Guard source-ordered actor dispatch and common successor/terminal contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_actor_return as prior
import verify_e1m1_aim_actor_dispatch as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorCycle\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimActorBoundary.Boundary E1M1AimActorCycle.Outcome
'''
class AimActorDispatchTests(unittest.TestCase):
    lean=prior.AimActorReturnTests.lean
    succeeds=prior.AimActorReturnTests.succeeds
    rejects=prior.AimActorReturnTests.rejects
    mutations=prior.AimActorReturnTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorCycle.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_linked_branch_bytes_remain_authenticated(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted()
        for name in ['aimActorGuard','aimActorReject','aimActorBottom','aimActorSelect']:
            bad=dict(raw);bad[name]=bytes([0x90])+raw[name][1:]
            self.rejects(proof.certificate(data,bad))
    def test_dispatch_preserves_eligibility_and_signed_equality(self):
        self.mutations(self.contract('E1M1AimActorDispatch','eligible','scene shooter hit lower upper topSlope bottomSlope different shootable'),[
            ('(different : hit.id≠shooter)','(different : True)'),
            ('(shootable : scene.things[hit.id]!.shootable=true)','(shootable : True)'),
            ('topSlope.raw<lower.raw','topSlope.raw≤lower.raw'),
            ('upper.raw<bottomSlope.raw','upper.raw≤bottomSlope.raw')])
    def test_common_cycle_requires_identity_history_and_division_correspondence(self):
        self.mutations(self.contract('E1M1AimActorCycle','execution',proof.EXEC_ARGS),[
            ('(history : History original.collected work seen visits)','(history : True)'),
            ('(identity : resolve original.collected[j]! = who ↔ (work[j]!).id=shooter)','(identity : True)'),
            ('(distance*(work[j]!).frac)=.ok topSlope','(distance*(work[j]!).frac)=.ok bottomSlope'),
            ('n≤115+7*work.size','n≤114+7*work.size'),
            ('(saveSafe : E1M1AimActorReturn.Safe s)','(saveSafe : True)')])
    def test_next_callback_requires_admitted_minimum_and_original_query(self):
        self.mutations(self.contract('E1M1AimActorBoundary','next_callback',proof.NEXT_ARGS),[
            ('(within : ¬fraction>65536)','(within : True)'),
            ('(chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j))','(chosen : True)'),
            ('(empty : original.visited=#[])','(empty : True)'),
            ('path.visited[seen.length]! = work[j]!','path.visited[seen.length+1]! = work[j]!')])
    def test_all_continuing_branches_require_their_real_machine_boundary(self):
        args='s scene shooter thing path original distance work seen visits resolve portals lower upper log out history empty query next'
        for method,owner in [('skipped','E1M1AimActorSkipCycle'),('top_rejected','E1M1AimActorRejectCycle'),('bottom_rejected','E1M1AimActorBottomCycle')]:
            self.mutations(self.contract('E1M1AimActorBoundary',method,args),[
                (f'(next : {owner}.Next s original.collected work seen resolve portals distance thing.shootHeight out)','(next : True)'),
                ('(history : History original.collected work seen visits)','(history : True)')])
    def test_common_boundary_reuses_line_interface(self):
        self.mutations(self.contract('E1M1AimActorBoundary','line_boundary',proof.NEXT_ARGS),[
            ('(within : ¬fraction>65536)','(within : True)'),
            ('(boundary : Doom.Proofs.E1M1AimActorBoundary.Boundary s scene shooter thing path original distance work seen resolve portals lower upper log out)','(boundary : True)'),
            ('resolve portals lower upper log out :=','resolve portals upper lower log out :=')])
    def test_short_circuit_order_and_signed_edge_examples(self):
        self.succeeds('import Doom.Proofs.E1M1AimActorCycle\n'+proof.HEADER+'''
open E1M1AimActorDispatch
example (scene : Scene) (hit : Intercept) (lo hi top bot : Fixed) :
    dispatch scene hit.id hit lo hi top bot=.ignored := by simp [dispatch]
example (scene : Scene) (shooter : Nat) (hit : Intercept) (lo hi top bot : Fixed)
    (h : scene.things[hit.id]!.shootable=false) :
    dispatch scene shooter hit lo hi top bot=.ignored := by simp [dispatch,h]
example (scene : Scene) (shooter : Nat) (hit : Intercept)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true) :
    dispatch scene shooter hit ⟨0⟩ ⟨0⟩ ⟨-1⟩ ⟨1⟩=.below := by
  rw [eligible scene shooter hit _ _ _ _ different shootable]; decide
example (scene : Scene) (shooter : Nat) (hit : Intercept)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true) :
    dispatch scene shooter hit ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩=.above := by
  rw [eligible scene shooter hit _ _ _ _ different shootable]; decide
example (scene : Scene) (shooter : Nat) (hit : Intercept)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true) :
    dispatch scene shooter hit ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩=.selected := by
  exact equality scene shooter hit _ _ different shootable
''')
if __name__=='__main__':unittest.main()

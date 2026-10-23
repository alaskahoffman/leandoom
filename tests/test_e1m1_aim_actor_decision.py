"""Regress actor provenance, direct pointer identity, and actual query decisions."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_selected_call as prior
import verify_e1m1_aim_actor_decision as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorDecision\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimActorDecisionTests(unittest.TestCase):
    lean=prior.AimSelectedCallTests.lean
    succeeds=prior.AimSelectedCallTests.succeeds
    rejects=prior.AimSelectedCallTests.rejects
    mutations=prior.AimSelectedCallTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorDecision.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_callback_needs_arithmetic_and_initial_null_target(self):
        self.mutations(self.contract('E1M1AimActorHit','execution'),[
            ('(arithmetic : Doom.Proofs.E1M1AimHitOutcome.Arithmetic scene shooter portals distance thing.shootHeight a j)','(arithmetic : True)'),
            ('(null : load32 s.memory (0x2b9f8#32)=0)','(null : True)')])
    def test_ordered_loop_needs_remaining_hit_budget(self):
        self.mutations(self.contract('E1M1AimActorOrdered','execution'),[
            ('(budget : fuel=original.collected.size-seen.length)','(budget : True)'),
            ('(history : History original.collected a.work seen visits)','(history : True)')])
    def test_return_requires_actor_tagged_exit(self):
        self.mutations(self.contract('E1M1AimActorCaller','returned'),[
            ('Doom.Proofs.E1M1AimActorHit.Exit initial resolve s answer','E1M1AimHitMemory.Exit initial resolve s answer')])
    def test_direct_pointer_cannot_use_old_untagged_image(self):
        self.mutations(self.contract('E1M1AimActorCaller','object_pointer'),[
            ('Doom.Proofs.E1M1AimActorCaller.Image initial','E1M1AimReturnedTarget.Image initial'),
            ('(chosen : answer.target=some id)','(chosen : True)'),
            ('0x2b9f8=objects id','0x2b9f8=objects (id+1)')])
    def test_actor_image_rejects_an_all_wall_hit_buffer(self):
        self.succeeds(HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) (id : Nat)
    (image : E1M1AimActorCaller.Image initial resolve out answer)
    (chosen : answer.target=some id)
    (walls : ∀ j<initial.size, initial[j]!.isLine=true) : False := by
  obtain ⟨j,bound,identity,kind,pointer,slope⟩ := image.selected id chosen
  rw [walls j bound] at kind
  cases kind
''')
    def test_null_target_permits_stale_aim_slope(self):
        self.succeeds(HEADER+'''
example (objects : Nat → Word) (out : X86Control.State) (angle : Angle)
    (null : load32 out.core.memory 0x2b9f8=0) :
    E1M1AimActorObservation.Observed objects out {facing:=angle} := by
  exact ⟨fun _ => null,fun _ h => by cases h⟩
''')
    def test_all_controller_return_adapters_retain_actor_image(self):
        for name in ['accepted','last']:
            with self.subTest(theorem=name):
                self.mutations(self.contract('E1M1AimActorObservation',name),[
                    ('(image : Doom.Proofs.E1M1AimActorCaller.Image initial resolve out answer)','(image : True)')])
        self.mutations(self.contract('E1M1AimActorDecision','decision_image'),[
            ('(image : E1M1AimActorCaller.Image initial resolve out answer)','(image : True)')])
    def test_source_window_requires_successful_live_query(self):
        self.mutations(self.contract('E1M1AimActorObservation','selection'),[
            ('(query : scene.aimLineAttack shooter probe (Fixed.ofInt 1024)=.ok answer)','(query : True)'),
            ('Doom.Proofs.E1M1AimActorCaller.Image initial','E1M1AimReturnedTarget.Image initial')])
    def test_last_controller_result_needs_prior_misses(self):
        self.mutations(self.contract('E1M1AimActorObservation','last_correspondence'),[
            ('(no0 : a.target.isSome=false)','(no0 : True)'),
            ('(no1 : b.target.isSome=false)','(no1 : True)')])
    def test_query_retains_real_return_and_source_slope(self):
        source=self.contract('E1M1AimActorQuery','execution')
        self.assertIn('E1M1AimActorCaller.Image after.collected',source)
        self.mutations(source,[
            ('⟨s,f,0x2c8a0⟩','⟨s,f,0x2bb80⟩'),
            ('out.core.regs 0=answer.slope.raw.toBitVec','out.core.regs 0=0')])
    def test_continuous_decision_exports_direct_pointer_and_real_branch(self):
        source=self.contract('E1M1AimActorDecision','execution')
        self.assertNotIn('(image :',source)
        self.assertNotIn('(answer : AimResult)',source.split(' :\n    let g :=')[0])
        self.assertIn('E1M1AimActorCaller.Image after.collected',source)
        self.mutations(source,[
            ('0x2b9f8=q.objects id','0x2b9f8=q.objects (id+1)'),
            ('out.pc=(if answer.target.isSome then 0x2d81e','out.pc=(if answer.target.isSome then 0x2d807'),
            ('0x2c0c0=answer.slope.raw.toBitVec','0x2c0c0=0')])
if __name__=='__main__':unittest.main()

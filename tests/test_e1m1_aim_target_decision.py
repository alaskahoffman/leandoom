"""Guard executed target provenance and zero-slope autoaim decisions."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_linked_query as prior
import verify_e1m1_aim_target_decision as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimTargetDecision\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimTargetDecisionTests(unittest.TestCase):
    lean=prior.AimLinkedQueryTests.lean
    succeeds=prior.AimLinkedQueryTests.succeeds
    rejects=prior.AimLinkedQueryTests.rejects
    mutations=prior.AimLinkedQueryTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_complete_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimReturnedTarget.probe','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_return_preserves_target_and_selected_record_image(self):
        self.mutations(self.contract('E1M1AimReturnedTarget','word'),[
            ('(safe : Apart a 0x2c028)','(safe : True)')])
        self.mutations(self.contract('E1M1AimReturnedTarget','returned'),[
            ('(exit : E1M1AimHitMemory.Exit initial resolve s answer)','(exit : True)'),
            ('Doom.Proofs.E1M1AimReturnedTarget.Image initial resolve (E1M1AimCompletedReturn.result s) answer',
             'Doom.Proofs.E1M1AimReturnedTarget.Image #[] resolve (E1M1AimCompletedReturn.result s) answer')])
    def test_probe_interface_needs_nonnull_pointer_encoding_and_actual_value(self):
        self.mutations(self.contract('E1M1AimReturnedTarget','probe'),[
            ('(nonnull : ∀ j<initial.size, resolve initial[j]!≠0)','(nonnull : True)'),
            ('(value : out.core.regs 0=answer.slope.raw.toBitVec)','(value : out.core.regs 1=answer.slope.raw.toBitVec)')])
    def test_zero_slope_does_not_mean_miss(self):
        self.mutations(self.contract('E1M1AimReturnedTarget','zero_slope_hit'),[
            ('(hit : answer.target.isSome=true)','(hit : True)'),
            ('out.core.regs 0=0 ∧ OriginalBulletSlope.target out.core≠0',
             'out.core.regs 0=0 ∧ OriginalBulletSlope.target out.core=0')])
        self.succeeds(HEADER+'''
example (out : X86Control.State) (answer : Collision.AimResult)
    (related : E1M1BulletAim.ProbeResult out.core answer)
    (hit : answer.target.isSome=true) (zero : answer.slope.raw.toBitVec=0) :
    out.core.regs 0=0 ∧ (OriginalBulletSlope.decision false out.core).pc=0x2d81e := by
  have pair := E1M1AimReturnedTarget.zero_slope_hit out answer related hit zero
  exact ⟨pair.1,by simp only [OriginalBulletSlope.decision,pair.2,if_false]⟩
''')
    def test_continuous_query_derives_complete_interface_at_its_own_endpoint(self):
        source=self.contract('E1M1AimQueryTarget')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(related :','(image :','(hit :','(run :']:
            self.assertNotIn(absent,args)
        self.mutations(source,[
            ('E1M1BulletAim.ProbeResult out.core answer','E1M1BulletAim.ProbeResult s answer'),
            ('Doom.Proofs.E1M1AimQueryCaller.Initial q s scene shooter thing after.collected distance portals walls who','True')])
    def test_actual_decision_uses_target_presence_and_stores_bullet_slope(self):
        self.mutations(self.contract('E1M1AimTargetDecision','decision'),[
            ('(resume : out.pc=if second then 0x2d7f8 else 0x2d7d5)','(resume : True)'),
            ('if answer.target.isSome then 0x2d81e else (if second then 0x2d807 else 0x2d7e4)',
             'if answer.target.isSome then 0x2d7e4 else (if second then 0x2d807 else 0x2d7e4)'),
            ('core.memory 0x2c0c0=answer.slope.raw.toBitVec','core.memory 0x2b9f8=answer.slope.raw.toBitVec')])
    def test_complete_query_decision_derives_landing_from_initial_saved_return(self):
        source=self.contract('E1M1AimTargetDecision')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(related :','(hit :','(run :']:
            self.assertNotIn(absent,args)
        self.assertIn('load32 s.memory ((q.sp-136)+112)',args)
        self.mutations(source,[
            ('(load32 s.memory ((q.sp-136)+112)).toNat','(load32 s.memory ((q.sp-136)+108)).toNat'),
            ('out.pc=(if answer.target.isSome then 0x2d81e','out.pc=(if answer.target.isSome then 0x2d819'),
            ('load32 out.core.memory 0x2c0c0=answer.slope.raw.toBitVec',
             'load32 s.memory 0x2c0c0=answer.slope.raw.toBitVec')])
if __name__=='__main__':unittest.main()

"""Regress the executed three-probe suffix, its source result and original-memory contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_pair_controller as prior
import verify_e1m1_aim_three_calls as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimThreeCalls\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimThreeCallsTests(unittest.TestCase):
    lean=prior.AimPairControllerTests.lean
    succeeds=prior.AimPairControllerTests.succeeds
    rejects=prior.AimPairControllerTests.rejects
    mutations=prior.AimPairControllerTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimThreeCalls.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_source_miss_requires_success_and_absence(self):
        self.mutations(self.contract('E1M1AimMissZero','aim'),[
            ('(run : scene.aimLineAttack shooter angle distance=.ok answer)','(run : True)'),
            ('(absent : answer.target=none)','(absent : True)'),
            ('answer.slope=⟨0⟩','answer.slope=Fixed.ofInt 1')])
    def test_loop_invariant_requires_actual_fold(self):
        self.mutations(self.contract('E1M1AimMissZero','loop_good'),[
            ('(good : Doom.Proofs.E1M1AimMissZero.Good state)','(good : True)'),
            ('(run : forIn indices state (visit scene shooter thing path distance)=Except.ok final)','(run : True)')])
    def test_third_geometry_needs_preserved_original_reads(self):
        self.mutations(self.contract('E1M1AimThirdCall','prepared'),[
            ('(tables : ThrustTables s.memory)','(tables : True)'),
            ('load32 third.core.memory a=load32 s.memory a','load32 third.core.memory a=load32 third.core.memory a')])
    def test_third_epoch_is_after_both_queries(self):
        self.mutations(self.contract('E1M1AimThirdCall','inputs'),[
            ('(epoch : load32 third.core.memory 0x13580=q.epoch+1)',
             '(epoch : load32 third.core.memory 0x13580=q.epoch)'),
            ('((q.epoch+1)+1) 475','(q.epoch+1) 475')])
    def test_third_call_uses_left_angle_and_original_return(self):
        self.mutations(self.contract('E1M1AimThirdCall','execution'),[
            ('out.pc=0x2d819','out.pc=0x2d7f8'),
            ('(request : Doom.Proofs.E1M1AimThirdCall.Request s third facing)','(request : True)')])
    def test_third_catalog_requires_original_word_coverage(self):
        self.mutations(self.contract('E1M1AimThirdCall','execution'),[
            ('(kept : ∀ a∈watched, load32 third.core.memory a=load32 s.memory a)','(kept : True)'),
            ('(∀ a∈E1M1AimRetryCatalog.reads after.collected (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) portals, a∈watched)',
             '(True)')])
    def test_join_has_no_assumed_reached_answers_or_zero_property(self):
        source=self.contract('E1M1AimThreeCalls','execution')
        premises=source.split(' :\n    ∃ (selected')[0]
        for name in ['answer','third','request','fresh','zero','related']:
            self.assertNotIn('('+name+' :',premises)
        self.assertIn('q.world.bulletAim shooter angle=.ok selected',source)
        self.mutations(source,[
            ('load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec',
             'load32 out.core.memory 0x2c0c0=0'),
            ('⟨s,f,0x2bb80⟩ out','⟨s,f,0x2d7d5⟩ out')])
    def test_join_requires_third_read_coverage(self):
        source=self.contract('E1M1AimThreeCalls','execution')
        start=source.index('    (thirdCovered :');end=source.index('    (thirdInitial :',start)
        self.mutations(source,[(source[start:end],'    (thirdCovered : True)\n')])
    def test_join_requires_original_two_ahead_freshness(self):
        self.mutations(self.contract('E1M1AimThreeCalls','execution'),[
            ('(beforeTwo : E1M1AimStampImage.Fresh s.memory q.lines ((q.epoch+1)+1) 475)',
             '(beforeTwo : True)'),
            ('(thirdRoom : budget (E1M1AimThirdCall.context q thing angle)\n      (E1M1AimThirdCall.route q thirdPick thing angle thirdX thirdY)≤128)',
             '(thirdRoom : True)')])
    def test_left_angle_wrap_and_zero_slope_present_target(self):
        self.succeeds(HEADER+'''
attribute [local semireducible] BitVec.add
example : (E1M1AimThirdCall.angle ⟨0x01000000⟩).raw=0xfd000000 := by decide
example : (E1M1AimThirdCall.angle ⟨0xffffffff⟩).raw=0xfbffffff := by decide
example (path : PathResult) : ({slope:=⟨0⟩,target:=some 4,path} : AimResult).target.isSome=true := rfl
example (path : PathResult) (top bottom : Fixed) (history : Array AutoAim.Portal) :
    E1M1AimMissZero.Good (some {slope:=⟨0⟩,target:=some 4,path},top,bottom,history) :=
  E1M1AimMissZero.hit_good _ _ _ _ _ _ _
''')
if __name__=='__main__':unittest.main()

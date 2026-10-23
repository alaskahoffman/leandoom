"""Regress live early autoaim exits and fresh, correctly angled third requests."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_retry_pair as prior
import verify_e1m1_aim_pair_controller as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimPairController\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimPairControllerTests(unittest.TestCase):
    lean=prior.AimRetryPairTests.lean
    succeeds=prior.AimRetryPairTests.succeeds
    rejects=prior.AimRetryPairTests.rejects
    mutations=prior.AimRetryPairTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimPairController.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_accepted_exit_requires_target_presence_not_zero_slope(self):
        self.mutations(self.contract('E1M1AimControllerExit','accepted'),[
            ('(hit : answer.target.isSome=true)','(hit : answer.slope=Fixed.ofInt 0)'),
            ('(resume : out.pc=if second then 0x2d7f8 else 0x2d7d5)','(resume : True)'),
            ('Apart a 0x2c0c0 →','True →')])
    def test_final_store_return_does_not_need_a_target_test(self):
        source=self.contract('E1M1AimControllerExit','last')
        self.assertNotIn('(hit :',source);self.assertNotIn('(miss :',source)
        self.mutations(source,[
            ('(resume : out.pc=0x2d819)','(resume : out.pc=0x2d7f8)'),
            ('=answer.slope.raw.toBitVec','=0')])
    def test_center_exit_requires_actual_source_query(self):
        self.mutations(self.contract('E1M1AimControllerExit','center'),[
            ('(query : scene.aimLineAttack shooter angle (Fixed.ofInt 1024)=.ok answer)','(query : True)'),
            ('BulletAim.selection angle 0 answer','BulletAim.selection angle 0x04000000 answer')])
    def test_right_exit_requires_center_miss_and_next_angle(self):
        self.mutations(self.contract('E1M1AimControllerExit','right'),[
            ('(miss : first.target=none)','(miss : first.slope=Fixed.ofInt 0)'),
            ('E1M1AimRetryGeometry.nextAngle false angle','E1M1AimRetryGeometry.nextAngle true angle')])
    def test_epoch_and_angle_arithmetic_includes_wraparound(self):
        self.succeeds('import Doom.Proofs.E1M1AimPairController\n'+proof.HEADER+'''
set_option maxRecDepth 32768
example : ((0xffffffff#32)+1)+1=1 := by decide
example : ((0xfffffffe#32)+1)+1=0 := by decide
example : (0xfffffffe#32)≠((0xfffffffe#32)+1)+1 := E1M1AimThirdRequest.two_ahead_ne _
example : (((0x01000000 : UInt32).toBitVec+0x04000000)+0xf8000000)=(0xfd000000#32) := by decide
example : (((0xffffffff : UInt32).toBitVec+0x04000000)+0xf8000000)=(0xfbffffff#32) := by decide
''')
        self.mutations(self.contract('E1M1AimThirdRequest','two_ahead_ne'),[
            ('epoch≠(epoch+1)+1','epoch≠epoch')])
    def test_two_histories_need_original_future_freshness(self):
        self.mutations(self.contract('E1M1AimThirdRequest','consecutive_fresh'),[
            ('(before : Doom.Proofs.E1M1AimStampImage.Fresh origin lines ((epoch+1)+1) count)',
             '(before : Doom.Proofs.E1M1AimStampImage.Fresh origin lines (epoch+1) count)'),
            ('(secondSize : second.size=count)','(secondSize : True)'),
            ('(firstImage : Doom.Proofs.E1M1AimStampImage.Image origin middle lines epoch first)','(firstImage : True)')])
    def test_retry_stores_require_stamp_separation(self):
        for name in ['retry_image','retry_fresh']:
            with self.subTest(theorem=name):
                self.mutations(self.contract('E1M1AimThirdRequest',name),[
                    ('(safe : ∀ a∈Doom.Proofs.E1M1AimStampQuery.stampWords lines count, Apart a 0x2c0c0 ∧ Apart a (out.core.regs 4-4))',
                     '(safe : True)')])
    def test_third_arguments_compose_both_real_requests(self):
        self.mutations(self.contract('E1M1AimThirdRequest','arguments'),[
            ('(first : E1M1AimRetryRequest.Request false s right)','(first : True)'),
            ('(angle.raw+0xfc000000).toBitVec','(angle.raw+0xf8000000).toBitVec'),
            ('third.core.regs 3=0x04000000','third.core.regs 3=0x08000000')])
    def test_joined_early_exits_use_production_bullet_aim(self):
        source=self.contract('E1M1AimPairController','execution')
        self.assertIn('q.world.bulletAim shooter angle=.ok (BulletAim.selection angle 0 answer)',source)
        self.assertIn('q.world.bulletAim shooter angle=.ok (BulletAim.selection angle 0x04000000 futureAnswer)',source)
        self.mutations(source,[
            ('(answer.target.isSome=true →','(answer.slope=Fixed.ofInt 0 →'),
            ('(((n+9)+m)+9)','(((n+9)+m)+8)')])
    def test_joined_third_entry_has_no_assumed_reached_freshness(self):
        source=self.contract('E1M1AimPairController','execution')
        args=source.split(' :\n    let g :=')[0]
        self.assertNotIn('(request :',args);self.assertNotIn('(fresh :',args);self.assertNotIn('(image :',args)
        self.assertIn('(((n+9)+m)+8)',source)
        self.mutations(source,[
            ('(beforeTwo : E1M1AimStampImage.Fresh s.memory q.lines ((q.epoch+1)+1) 475)',
             '(beforeTwo : True)'),
            ('load32 third.core.memory (third.core.regs 4)=0x2d819',
             'load32 third.core.memory (third.core.regs 4)=0x2d7f8')])
    def test_joined_third_entry_retains_second_history_and_origin(self):
        self.mutations(self.contract('E1M1AimPairController','execution'),[
            ('E1M1AimStampImage.Image next.core.memory third.core.memory',
             'E1M1AimStampImage.Image s.memory third.core.memory'),
            ('E1M1AimStampImage.Fresh third.core.memory q.lines ((q.epoch+1)+1) 475',
             'E1M1AimStampImage.Fresh third.core.memory q.lines (q.epoch+1) 475')])
if __name__=='__main__':unittest.main()

"""Regress the actual aim-entry join and keep its residual assumptions visible."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_target_decision as prior
import verify_e1m1_aim_entry_query as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimEntryQuery\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimEntryQueryTests(unittest.TestCase):
    lean=prior.AimTargetDecisionTests.lean
    succeeds=prior.AimTargetDecisionTests.succeeds
    rejects=prior.AimTargetDecisionTests.rejects
    mutations=prior.AimTargetDecisionTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimSetupLink.ray','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_actual_setup_program_and_instruction_count(self):
        self.succeeds(self.contract('E1M1AimSetupLink','ray'))
        self.succeeds(self.contract('E1M1AimSetupLink','setup'))
        self.mutations(self.contract('E1M1AimSetupLink'),[
            ('program [] 36','program [] 35'),('⟨s,f,0x2bb80⟩','⟨s,f,0x2bba0⟩')])
        self.mutations(HEADER+'''
example : E1M1AimProgramLink.program 0x2bbfa=some (.prior (.call 0xca1),5) := by decide
''',[
            ('.call 0xca1','.call 0xca0'),('0xca1),5','0xca1),4')])
    def test_derived_entry_requires_pre_ray_inputs_and_correct_endpoint(self):
        self.mutations(self.contract('E1M1AimSetupEntry','entry'),[
            ('(h : Doom.Proofs.E1M1AimSetupEntry.Inputs q s thing angle distance)','(h : True)'),
            ('Entry q (Doom.Proofs.E1M1PathMapQuery.traversal s).core thing.x thing.y',
             'Entry q s thing.x thing.y')])
    def test_setup_generates_actual_callback_flags_and_globals(self):
        self.mutations(self.contract('E1M1AimSetupEntry','call'),[
            ('=(0x2bbff,3,0x2b760)','=(0x2bbff,1,0x2b760)'),
            ('=(0x2bbff,3,0x2b760)','=(0x2bbff,3,0x2b761)')])
        self.mutations(self.contract('E1M1AimSetupEntry','globals'),[
            ('memory 0x2b9f8=0','memory 0x2b9f8=1'),
            ('memory 0x2b9b8=distance.raw.toBitVec','memory 0x2b9a8=distance.raw.toBitVec')])
        self.mutations(self.contract('E1M1AimSetupCatalog','initial'),[
            ('(h : E1M1AimSetupEntry.Inputs q s thing angle distance)','(h : True)')])
    def test_original_return_word_needs_protection_and_stack_relation(self):
        self.mutations(self.contract('E1M1AimSetupCatalog','return_address'),[
            ('(safe : E1M1PathMapQuery.Safe s (s.regs 4))','(safe : True)'),
            ('(stack : s.regs 4=q.sp-24)','(stack : s.regs 4=q.sp-28)'),
            ('memory ((q.sp-136)+112)','memory ((q.sp-136)+108)')])
    def test_full_production_source_needs_valid_shooter_positive_range_and_same_path(self):
        self.mutations(self.contract('E1M1AimEntryQuery','production'),[
            ('(positive : ¬distance.raw≤0)','(positive : True)'),
            ('(shooterValue : scene.things[shooter]?=some thing)','(shooterValue : True)'),
            ('scene.aimLineAttack shooter angle distance=.ok answer','scene.aimLineAttack (shooter+1) angle distance=.ok answer')])
    def test_continuous_entry_result_retains_explicit_residual_contracts(self):
        source=self.contract('E1M1AimEntryQuery')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(run :','(entry :','(argument :']:
            self.assertNotIn(absent,args)
        self.assertIn('E1M1AimSetupCatalog.Remaining',args)
        self.assertIn('E1M1QueryImages.Payload (Doom.Proofs.E1M1PathMapQuery.traversal s).core.memory',args)
        self.mutations(source,[
            ('program [] n ⟨s,f,0x2bb80⟩ out','program [] n ⟨s,f,0x2bba0⟩ out'),
            ('E1M1BulletAim.ProbeResult out.core answer','E1M1BulletAim.ProbeResult s answer'),
            ('E1M1AimSetupCatalog.Remaining q (Doom.Proofs.E1M1PathMapQuery.traversal s).core q.world shooter after.collected portals walls who','True')])
    def test_controller_resumes_from_original_return_and_stores_same_source_slope(self):
        self.mutations(self.contract('E1M1AimEntryQuery','decision'),[
            ('(load32 s.memory (s.regs 4)).toNat','(load32 s.memory (s.regs 4+4)).toNat'),
            ('memory 0x2c0c0=answer.slope.raw.toBitVec','memory 0x2b9f8=answer.slope.raw.toBitVec'),
            ('if answer.target.isSome then 0x2d81e','if answer.target.isSome then 0x2d7e4')])
if __name__=='__main__':unittest.main()

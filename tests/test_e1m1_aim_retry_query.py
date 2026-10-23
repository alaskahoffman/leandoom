"""Regress original caller provenance and actual miss-to-next-query execution."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_pre_ray_query as prior
import verify_e1m1_aim_retry_query as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimRetryQuery\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight BitVec.add
'''
class AimRetryQueryTests(unittest.TestCase):
    lean=prior.AimPreRayQueryTests.lean
    succeeds=prior.AimPreRayQueryTests.succeeds
    rejects=prior.AimPreRayQueryTests.rejects
    mutations=prior.AimPreRayQueryTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimCallerRegisters.restores','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_actual_saves_have_original_register_values(self):
        self.mutations(self.contract('E1M1AimCallerRegisters','saved'),[
            ('(s.regs 4-16)=s.regs 5','(s.regs 4-16)=s.regs 7'),
            ('(s.regs 4-8)=s.regs 6','(s.regs 4-8)=s.regs 0')])
        self.mutations(self.contract('E1M1AimCallerRegisters','setup_saved'),[
            ('(safe : Doom.Proofs.E1M1AimCallerRegisters.SavedSafe s)','(safe : True)')])
    def test_restoration_needs_initial_protection_and_original_stack(self):
        self.mutations(self.contract('E1M1AimCallerRegisters','restores'),[
            ('(returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))','(returnSafe : True)'),
            ('(stack : s.regs 4=q.sp-24)','(stack : s.regs 4=q.sp-28)'),
            ('(safe : Doom.Proofs.E1M1AimCallerRegisters.SavedSafe s)','(safe : True)')])
    def test_retry_execution_requires_actual_miss_and_correct_landing(self):
        self.mutations(self.contract('E1M1AimRetryRequest','execution'),[
            ('(miss : answer.target=none)','(miss : True)'),
            ('(resume : out.pc=if second then 0x2d7f8 else 0x2d7d5)','(resume : True)'),
            ('(4+(if second then 4 else 5))','(4+(if second then 5 else 4))')])
    def test_retry_request_uses_restored_actor_angle_and_stack(self):
        self.mutations(self.contract('E1M1AimRetryRequest','request'),[
            ('(restored : E1M1AimCallerRegisters.Restores s out)','(restored : True)')])
        self.mutations(HEADER+'''
example (s : X86Memory.State) (next : X86Control.State)
    (r : E1M1AimRetryRequest.Request false s next) :
    next.core.regs 0=s.regs 6 ∧ next.core.regs 2=s.regs 1+0x04000000 ∧ next.core.regs 4=s.regs 4 :=
  ⟨r.actor,r.angle,r.stack⟩
example (s : X86Memory.State) (next : X86Control.State)
    (r : E1M1AimRetryRequest.Request true s next) :
    next.core.regs 2=s.regs 1+0xf8000000 ∧ load32 next.core.memory (next.core.regs 4)=0x2d819 :=
  ⟨r.angle,r.returnWord⟩
''',[
            ('next.core.regs 0=s.regs 6','next.core.regs 0=s.regs 0'),
            ('s.regs 1+0xf8000000','s.regs 1+0xfc000000'),
            ('=0x2d819','=0x2d7f8')])
    def test_retry_memory_frame_covers_only_its_two_actual_writes(self):
        self.mutations(self.contract('E1M1AimRetryRequest','memory'),[
            ('(out.regs 4-4)','(out.regs 4-8)'),
            ('0x2c0c0 (out.regs 0)','0x2b9f8 (out.regs 0)')])
        self.mutations(self.contract('E1M1AimRetryRequest','frame'),[
            ('(slopeSafe : Apart a 0x2c0c0)','(slopeSafe : True)'),
            ('(returnSafe : Apart a (out.regs 4-4))','(returnSafe : True)')])
    def test_complete_query_exposes_original_caller_restoration(self):
        source=self.contract('E1M1AimRetryQuery','execution')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(restored :','traversal s']:
            self.assertNotIn(absent,args)
        self.mutations(source,[
            ('(savedSafe : E1M1AimCallerRegisters.SavedSafe s)','(savedSafe : True)'),
            ('E1M1AimCallerRegisters.Restores s out','E1M1AimCallerRegisters.Restores out.core out')])
    def test_complete_retry_is_conditional_and_continuous(self):
        source=self.contract('E1M1AimRetryQuery','retry')
        args=source.split(' :\n    let g :=')[0]
        self.assertNotIn('(miss :',args)
        self.assertIn('(answer.target=none →',source)
        self.mutations(source,[
            ('(n+(4+(if second then 4 else 5)))','(n+(4+(if second then 5 else 4)))'),
            ('(controller : s.regs 6=s.regs 0 ∧ s.regs 1=angle.raw.toBitVec)','(controller : True)'),
            ('(load32 s.memory (s.regs 4)).toNat','(load32 s.memory (s.regs 4+4)).toNat')])
if __name__=='__main__':unittest.main()

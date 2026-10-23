"""Regress original-memory input transport through the five controller writes."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_actor_controller as prior
import verify_e1m1_aim_original_inputs as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimOriginalInputs\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimOriginalInputsTests(unittest.TestCase):
    lean=prior.AimActorControllerTests.lean
    succeeds=prior.AimActorControllerTests.succeeds
    rejects=prior.AimActorControllerTests.rejects
    mutations=prior.AimActorControllerTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimOriginalInputs.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_layout_is_original_memory_even_with_wrapping_stack(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (angle : Angle) :
    (E1M1AimControllerInputs.layout s angle).memory=s.memory := rfl
example (s : X86Memory.State) (angle : Angle) (sp : s.regs 4=8) :
    (E1M1AimControllerInputs.layout s angle).regs 4=0xfffffff4 := by
  simp only [E1M1AimControllerInputs.layout,put,write,ite_false,ite_true]
  rw [sp]; rfl
''')
    def test_protection_rejects_actual_prologue_write_alias(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) :
    ¬E1M1AimControllerInputs.SafeReads s [s.regs 4-20] := by
  intro safe
  have h := safe (s.regs 4-20) (by simp) (s.regs 4-20)
    (by simp [E1M1AimControllerEntry.writes])
  exact h 0 0 rfl
''')
    def test_actual_register_layout_needs_original_angle_and_guard(self):
        self.mutations(self.contract('E1M1AimControllerInputs','registers'),[
            ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
            ('(safe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b)','(safe : True)')])
    def test_kept_reads_require_prologue_separation(self):
        self.mutations(self.contract('E1M1AimControllerInputs','kept'),[
            ('(safe : Doom.Proofs.E1M1AimControllerInputs.SafeReads s addresses)','(safe : True)')])
    def test_blockmap_requires_original_image_and_read_protection(self):
        self.mutations(self.contract('E1M1AimControllerInputs','map'),[
            ('(before : E1M1PathMapQuery.MapInputs (Doom.Proofs.E1M1AimControllerInputs.layout s angle) base lines words width height)','(before : True)'),
            ('(safe : Doom.Proofs.E1M1AimControllerInputs.SafeReads s (E1M1AimRetryData.mapReads base words))','(safe : True)')])
    def test_cell_payload_requires_finite_read_protection(self):
        self.mutations(self.contract('E1M1AimControllerInputs','payload'),[
            ('(safe : Doom.Proofs.E1M1AimControllerInputs.SafeReads s (E1M1AimRetryData.cellReads q c))','(safe : True)')])
    def test_actor_opening_catalog_requires_read_protection(self):
        self.mutations(self.contract('E1M1AimControllerInputs','catalog'),[
            ('(safe : Doom.Proofs.E1M1AimControllerInputs.SafeReads s (E1M1AimRetryCatalog.reads hits (E1M1ThingFinish.resolve q.lines q.objects) portals))','(safe : True)')])
    def test_setup_transports_current_counter_and_freshness(self):
        source=self.contract('E1M1AimControllerSetup','setup')
        self.mutations(source,[
            ('(safe : Doom.Proofs.E1M1AimControllerInputs.SafeReads s (Doom.Proofs.E1M1AimControllerSetup.reads q s angle))','(safe : True)'),
            ('(before : E1M1AimSetupEntry.Inputs q (Doom.Proofs.E1M1AimControllerInputs.layout s angle) thing angle (Fixed.ofInt 1024))','(before : True)')])
    def test_join_has_only_original_memory_contracts_and_same_conclusion(self):
        new=(ROOT/'Doom/Proofs/E1M1AimOriginalInputs.lean').read_text()
        old=(ROOT/'Doom/Proofs/E1M1AimActorController.lean').read_text()
        binders='\n'.join(prior.input_binders(new,'execution'))
        self.assertNotIn('E1M1AimControllerEntry.entry',binders)
        self.assertNotIn('(regs :',binders)
        self.assertIn('E1M1QueryImages.Payload s.memory',binders)
        self.assertIn('(h : E1M1AimSetupEntry.Inputs q (layout s angle)',binders)
        def result(source):
            decl=source[source.index('theorem execution '):].split(' := by',1)[0]
            return decl[decl.index(' :\n    ∃ (selected'):]
        self.assertEqual(result(new),result(old))
    def test_join_cannot_drop_setup_payload_or_catalog_guards(self):
        self.mutations(self.contract('E1M1AimOriginalInputs','execution'),[
            ('(setupSafe : Doom.Proofs.E1M1AimControllerInputs.SafeReads s (E1M1AimControllerSetup.reads q s angle))','(setupSafe : True)'),
            ('Doom.Proofs.E1M1AimControllerInputs.SafeReads s (E1M1AimRetryData.cellReads q c)','True'),
            ('Doom.Proofs.E1M1AimControllerInputs.SafeReads s (E1M1AimRetryCatalog.reads after.collected (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) portals)','True')])
    def test_final_actor_pointer_slope_and_outer_return_remain_exact(self):
        self.mutations(self.contract('E1M1AimOriginalInputs','execution'),[
            ('E1M1AimActorObservation.Observed q.objects out selected','E1M1AimActorObservation.Observed (fun _ => 0) out selected'),
            ('load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec','load32 out.core.memory 0x2c0c0=0'),
            ('out.core.regs 4=s.regs 4+4','out.core.regs 4=s.regs 4'),
            ('out.pc=(load32 s.memory (s.regs 4)).toNat','out.pc=0x2d7d5')])
if __name__=='__main__':unittest.main()

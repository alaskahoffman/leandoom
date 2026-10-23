"""Regress returned target encoding and original-memory table/stamp transport."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_controller_call as prior
import verify_e1m1_aim_selected_call as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimSelectedCall\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimSelectedCallTests(unittest.TestCase):
    lean=prior.AimControllerCallTests.lean
    succeeds=prior.AimControllerCallTests.succeeds
    rejects=prior.AimControllerCallTests.rejects
    mutations=prior.AimControllerCallTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimSelectedCall.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_source_window_identity_requires_actual_success(self):
        self.mutations(self.contract('E1M1AimWindowTarget','aim'),[
            ('(run : scene.aimLineAttack shooter angle distance=.ok answer)','(run : True)'),
            ('answer.target=answer.window.map AutoAim.Window.target','answer.target=none')])
    def test_target_frame_requires_both_globals(self):
        self.mutations(self.contract('E1M1AimControllerTarget','frame'),[
            ('(target : load32 next.core.memory 0x2b9f8=load32 out.core.memory 0x2b9f8)','(target : True)'),
            ('(slope : load32 next.core.memory 0x2b9b4=load32 out.core.memory 0x2b9b4)','(slope : True)')])
    def test_both_returns_retain_existing_target_image(self):
        for name in ['accepted','last']:
            with self.subTest(theorem=name):
                source=self.contract('E1M1AimControllerTarget',name)
                self.assertNotIn('(hit :',source)
                self.mutations(source,[
                    ('(image : Doom.Proofs.E1M1AimReturnedTarget.Image initial resolve out answer)','(image : True)')])
    def test_selection_derives_window_target_from_live_query(self):
        source=self.contract('E1M1AimControllerTarget','selection')
        self.assertNotIn('(same :',source)
        self.mutations(source,[
            ('(query : scene.aimLineAttack shooter probe (Fixed.ofInt 1024)=.ok answer)','(query : True)')])
    def test_miss_does_not_erase_a_present_target(self):
        self.mutations(self.contract('E1M1AimControllerTarget','miss'),[
            ('(absent : answer.target=none)','(absent : True)')])
    def test_last_correspondence_needs_both_earlier_misses(self):
        source=self.contract('E1M1AimControllerTarget','last_correspondence')
        self.assertNotIn('(zero :',source)
        self.mutations(source,[
            ('(no0 : a.target.isSome=false)','(no0 : True)'),
            ('(no1 : b.target.isSome=false)','(no1 : True)'),
            ('(image : Doom.Proofs.E1M1AimReturnedTarget.Image initial resolve out c)','(image : True)')])
    def test_original_tables_need_image_and_five_write_protection(self):
        self.mutations(self.contract('E1M1AimControllerData','tables'),[
            ('(before : ThrustTables s.memory)','(before : True)'),
            ('(safe : Doom.Proofs.E1M1AimControllerData.TableSafe s)','(safe : True)')])
    def test_original_freshness_needs_protected_stamps(self):
        self.mutations(self.contract('E1M1AimControllerData','fresh'),[
            ('(before : E1M1AimStampImage.Fresh s.memory lines epoch count)','(before : True)'),
            ('(safe : ∀ j<count, ∀ b∈Doom.Proofs.E1M1AimControllerEntry.writes s, Apart (OriginalLineVisits.stamp lines j) b)','(safe : True)')])
    def test_counter_transport_needs_original_value(self):
        self.mutations(self.contract('E1M1AimControllerData','counter'),[
            ('(before : load32 s.memory 0x13580=epoch)','(before : True)'),
            ('(safe : ∀ b∈Doom.Proofs.E1M1AimControllerEntry.writes s, Apart 0x13580 b)','(safe : True)')])
    def test_join_uses_pre_prologue_tables_and_freshness(self):
        source=self.contract('E1M1AimSelectedCall','execution')
        self.assertIn('(tables : ThrustTables s.memory)',source)
        self.assertIn('(beforeTwo : E1M1AimStampImage.Fresh s.memory q.lines ((q.epoch+1)+1) 475)',source)
        self.mutations(source,[
            ('(tableSafe : E1M1AimControllerData.TableSafe s)','(tableSafe : True)'),
            ('(freshSafe : ∀ j<475, ∀ b∈E1M1AimControllerEntry.writes s,\n      Apart (OriginalLineVisits.stamp q.lines j) b)','(freshSafe : True)')])
    def test_join_retains_target_encoding_and_caller_guarantees(self):
        source=self.contract('E1M1AimSelectedCall','execution')
        self.assertIn('E1M1AimControllerTarget.Observed initial (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) out selected',source)
        self.mutations(source,[
            ('out.pc=(load32 s.memory (s.regs 4)).toNat','out.pc=0x2d7d5'),
            ('out.core.regs 4=s.regs 4+4','out.core.regs 4=s.regs 4'),
            ('load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec','load32 out.core.memory 0x2c0c0=0')])
    def test_null_target_allows_stale_aim_slope_global(self):
        self.succeeds(HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State)
    (angle : Angle) (null : load32 out.core.memory 0x2b9f8=0) :
    E1M1AimControllerTarget.Observed initial resolve out {facing:=angle} := by
  exact ⟨fun _ => null,fun _ h => by cases h⟩
''')
if __name__=='__main__':unittest.main()

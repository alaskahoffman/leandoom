"""Regress direct actor correspondence through all probes and the caller return."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_actor_decision as prior
import verify_e1m1_aim_actor_controller as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimActorController\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
def input_binders(source,name):
    tail=source[source.index('theorem '+name+' ')+len('theorem '+name):]
    i=0;out=[]
    while i<len(tail):
        if tail[i].isspace():i+=1;continue
        if tail[i]==':':return out
        if tail[i]!='(':raise AssertionError(tail[i:i+60])
        start=i;i+=1;depth=1
        while depth:
            if tail[i]=='(':depth+=1
            elif tail[i]==')':depth-=1
            i+=1
        out.append(tail[start:i])
    raise AssertionError('missing result type')
class AimActorControllerTests(unittest.TestCase):
    lean=prior.AimActorDecisionTests.lean
    succeeds=prior.AimActorDecisionTests.succeeds
    rejects=prior.AimActorDecisionTests.rejects
    mutations=prior.AimActorDecisionTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimActorController.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_all_ten_strengthened_theorems_have_unchanged_inputs(self):
        for module,names in proof.GROUPS.items():
            old=(ROOT/f'Doom/Proofs/{proof.PREVIOUS_MODULES[module]}.lean').read_text()
            new=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
            for name in names:
                with self.subTest(module=module,theorem=name):
                    self.assertEqual(input_binders(new,name),input_binders(old,name))
    def test_query_return_preserves_protected_caller_words(self):
        self.mutations(self.contract('E1M1AimActorCallerFrame','execution'),[
            ('(watchedCursor : ∀ addr∈watched, Apart addr 0x2c028)','(watchedCursor : True)'),
            ('(null : load32 s.core.memory (0x2b9f8#32)=0)','(null : True)')])
    def test_stamp_query_needs_stamp_write_protection(self):
        self.mutations(self.contract('E1M1AimActorStampQuery','execution'),[
            ('(stampProtected : ∀ a∈Doom.Proofs.E1M1AimStampQuery.stampWords q.lines 475, E1M1AimSavedWords.Protect (Doom.Proofs.E1M1AimQueryCatalog.view q s) a)','(stampProtected : True)')])
    def test_preray_query_keeps_real_entry_and_source_result(self):
        source=self.contract('E1M1AimActorStampCall','execution')
        self.assertIn('E1M1AimActorCaller.Image after.collected',source)
        self.mutations(source,[
            ('[] n ⟨s,f,0x2bb80⟩ out','[] n ⟨s,f,0x2c8a0⟩ out'),
            ('q.world.aimLineAttack shooter angle distance=.ok answer','q.world.aimLineAttack shooter angle (Fixed.ofInt 1)=.ok answer')])
    def test_retry_requires_miss_and_preserves_stamp_epoch(self):
        self.mutations(self.contract('E1M1AimActorStampCall','retry'),[
            ('(answer.target=none →','(True →'),
            ('q.lines q.epoch\n          (history','q.lines (q.epoch+1)\n          (history')])
    def test_next_query_needs_freshness_and_actual_read_image(self):
        self.mutations(self.contract('E1M1AimActorNextCall','execution'),[
            ('(before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)','(before : True)'),
            ('(kept : ∀ a∈watched, load32 next.core.memory a=load32 s.memory a)','(kept : True)')])
    def test_retry_pair_carries_both_images_and_correct_return(self):
        source=self.contract('E1M1AimActorRetryPair','execution')
        self.assertEqual(source.count('E1M1AimActorCaller.Image '),2)
        self.mutations(source,[
            ('finish.pc=(if second then 0x2d819 else 0x2d7f8)','finish.pc=0x2d819'),
            ('(answer.target=none →','(True →')])
    def test_third_call_needs_derived_epoch_and_freshness(self):
        self.mutations(self.contract('E1M1AimActorThirdCall','execution'),[
            ('(epoch : load32 third.core.memory 0x13580=q.epoch+1)','(epoch : True)'),
            ('(fresh : E1M1AimStampImage.Fresh third.core.memory q.lines ((q.epoch+1)+1) 475)','(fresh : True)')])
    def test_pair_controller_needs_second_future_epoch(self):
        self.mutations(self.contract('E1M1AimActorPairController','execution'),[
            ('(beforeTwo : E1M1AimStampImage.Fresh s.memory q.lines ((q.epoch+1)+1) 475)','(beforeTwo : True)')])
    def test_join_exports_exact_object_mapping_without_record_witness(self):
        source=self.contract('E1M1AimActorController','execution')
        self.assertIn('E1M1AimActorObservation.Observed q.objects out selected',source)
        self.assertNotIn('∃ initial : Array Intercept',source)
        self.mutations(source,[
            ('E1M1AimActorObservation.Observed q.objects out selected','E1M1AimActorObservation.Observed (fun _ => 0) out selected'),
            ('load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec','load32 out.core.memory 0x2c0c0=0')])
    def test_join_retains_entry_pc_stack_registers_and_return(self):
        self.mutations(self.contract('E1M1AimActorController','execution'),[
            ('[] n ⟨s,f,0x2d7c0⟩ out','[] n ⟨s,f,0x2bb80⟩ out'),
            ('out.core.regs 4=s.regs 4+4','out.core.regs 4=s.regs 4'),
            ('out.core.regs 6=s.regs 6','out.core.regs 6=s.regs 0'),
            ('out.pc=(load32 s.memory (s.regs 4)).toNat','out.pc=0x2d7d5')])
    def test_final_observation_exposes_pointer_and_allows_stale_miss_slope(self):
        self.succeeds(HEADER+'''
example (objects : Nat → Word) (out : X86Control.State) (selected : AutoAim.Selection)
    (observed : E1M1AimActorObservation.Observed objects out selected)
    (window : AutoAim.Window) (hit : selected.window=some window) :
    load32 out.core.memory 0x2b9f8=objects window.target ∧
    load32 out.core.memory 0x2b9b4=selected.slope.raw.toBitVec := observed.selected window hit
example (objects : Nat → Word) (out : X86Control.State) (angle : Angle)
    (null : load32 out.core.memory 0x2b9f8=0) :
    E1M1AimActorObservation.Observed objects out {facing:=angle} := by
  exact ⟨fun _ => null,fun _ h => by cases h⟩
''')
if __name__=='__main__':unittest.main()

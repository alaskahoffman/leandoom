"""Saved caller boundaries, selected-actor stores and retained return obligations."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_callback_entry as prior
import verify_e1m1_aim_saved_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimSavedEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimSavedEntryTests(unittest.TestCase):
    lean=prior.AimCallbackEntryTests.lean
    succeeds=prior.AimCallbackEntryTests.succeeds
    rejects=prior.AimCallbackEntryTests.rejects
    mutations=prior.AimCallbackEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimSavedEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_ordered_stack_boundary_and_wrapping_translation(self):
        self.succeeds(HEADER+'''
example (sp : Word) : Apart (sp-136) (sp+(-140#32)) :=
  E1M1AimSavedRegions.above sp 136 (-140#32) (by decide) (by decide) (by decide)
example : Apart (0-136 : Word) (0+(-140#32)) :=
  E1M1AimSavedRegions.above 0 136 (-140#32) (by decide) (by decide) (by decide)
example : ¬Apart (1000-137 : Word) (1000-140) := by unfold Apart; decide
example (s : X86Memory.State) : ¬E1M1AimSavedWords.Protect s (s.regs 4) := by
  intro h
  exact h.1.2.2.2 0 0 rfl
''')
    def test_positive_outer_save_protected_through_actor_selection(self):
        self.succeeds(HEADER+'''
def state : X86Memory.State := ⟨fun _ => 972,fun _ => 0⟩
example : E1M1AimSavedWords.Protect state (1112-120) := by
  exact E1M1AimSavedRegions.protect ⟨900,1112⟩ 1112 4096 state 120
    ⟨by decide,by decide,by decide⟩
    (by unfold E1M1AimWalkRegions.Reserve; decide) rfl (by decide) (by decide)
example : E1M1AimSavedCaller.words (1112-136)=
    [(1112-120#32),1112-116,1112-52,1112-40,1112-36,1112-32,1112-28,1112-24] := by decide
''')
    def test_actor_target_store_cannot_alias_callback_return(self):
        self.succeeds(HEADER+'''
def state : X86Memory.State := ⟨fun _ => 0x2b9f8,fun _ => 0⟩
example : ¬E1M1AimActorReturn.Safe state := by
  intro h
  have hit := (h 0 (by simp [E1M1AimReturnFrame.slots])).1
  exact hit 0 0 rfl
example : ¬Apart (0x2b9b4#32) (0x2b9b4#32) := by unfold Apart; decide
''')
    def test_byte_bound_and_stack_placement_cannot_be_weakened(self):
        self.mutations(self.contract('E1M1AimSavedRegions','above'),[
          ('(high : n≤136)','(high : n≤137)'),
          ('off.toNat≤2^32-140','off.toNat≤2^32-139')])
        self.mutations(self.contract('E1M1AimSavedRegions','ordered'),[
          ('(position : s.regs 4=sp-140)','(position : True)'),
          ('(placement : Doom.Proofs.E1M1AimCallbackRegions.Layout stack lines)','(placement : True)')])
    def test_actor_return_requires_global_stack_separation(self):
        self.mutations(self.contract('E1M1AimSavedRegions','actor_return'),[
          ('(placement : Doom.Proofs.E1M1AimCallbackRegions.Layout stack q.lines)','(placement : True)'),
          ('(position : s.regs 4=q.sp-140)','(position : True)')])
    def test_restoration_keeps_image_and_actual_final_stack(self):
        self.mutations(self.contract('E1M1AimSavedRegions','restores'),[
          ('(image : E1M1AimSavedCaller.Image start finish (q.sp-136))','(image : True)'),
          ('(finished : finish.core.regs 4=q.sp-136)','(finished : True)')])
    def test_residual_catalog_retains_every_other_field(self):
        def fields(module):
            s=(ROOT/f'Doom/Proofs/{module}.lean').read_text().split('structure OtherInputs',1)[1].split('\n\n',1)[0]
            return re.findall(r'^  (\w+) :',s,re.M)
        before=fields('E1M1AimCatalogEntry');after=fields('E1M1AimSavedEntry')
        self.assertEqual(after,[x for x in before if x not in ['saveSafe','savedSafe']])
        self.assertIn('callerReads',after)
        self.mutations(self.contract('E1M1AimSavedEntry','other'),[
          ('(input : Doom.Proofs.E1M1AimSavedEntry.OtherInputs q s scene shooter hits portals walls who)','(input : True)')])
    def test_catalog_joins_retain_both_region_families(self):
        for name in ['initial','remaining','controller']:
            decl=proof.declaration('E1M1AimSavedEntry',name)
            self.assertIn('E1M1AimStampRegions.Layout',decl)
            self.assertIn('E1M1AimCallbackRegions.Layout',decl)
        self.mutations(self.contract('E1M1AimSavedEntry','initial'),[
          ('(callerPlacement : E1M1AimCallbackRegions.Layout stack q.lines)','(callerPlacement : True)'),
          ('(walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)','(walkReserve : True)')])
    def test_outer_controller_retains_original_angle(self):
        self.mutations(self.contract('E1M1AimSavedEntry','controller'),[
          ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)')])
if __name__=='__main__':unittest.main()

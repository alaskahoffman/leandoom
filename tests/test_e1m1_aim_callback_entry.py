"""Callback-pointer, selector-buffer and upper-caller stack protection."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_cell_collection as prior
import verify_e1m1_aim_callback_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCallbackEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimCallbackEntryTests(unittest.TestCase):
    lean=prior.AimCellCollectionTests.lean
    succeeds=prior.AimCellCollectionTests.succeeds
    rejects=prior.AimCellCollectionTests.rejects
    mutations=prior.AimCellCollectionTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimCallbackEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_caller_boundary_and_wrapping_translation(self):
        self.succeeds(HEADER+'''
example (sp : Word) : Apart (sp-64) (sp+(-68#32)) :=
  E1M1AimCallbackRegions.above sp 64 (-68#32) (by decide) (by decide) (by decide)
example : Apart (0-64 : Word) (0+(-68#32)) :=
  E1M1AimCallbackRegions.above 0 64 (-68#32) (by decide) (by decide) (by decide)
example : ¬Apart (1000-65 : Word) (1000-68) := by unfold Apart; decide
example (lines : Word) : ¬E1M1FiringMapState.Safe 1000 lines (1000-65) := by
  intro h
  have overlap : ¬Apart (1000-65 : Word) (1000-112+44) := by unfold Apart; decide
  exact overlap h.advance
''')
    def test_positive_saved_callback_collection_guard(self):
        self.succeeds(HEADER+'''
example : E1M1FiringMapState.Safe 1112 4096 (1112-44) := by
  exact E1M1AimCallbackRegions.upper_collection ⟨900,1112⟩ 1112 4096 44
    ⟨by decide,by decide,by decide⟩
    (by unfold E1M1AimWalkRegions.Reserve; decide) (by decide) (by decide)
example : (⟨900,1112⟩ : Region).Contains (1112-212) :=
  E1M1AimCallbackRegions.stack_word ⟨900,1112⟩ 1112 212
    (by unfold E1M1AimWalkRegions.Reserve; decide) (by decide) (by decide)
example : ¬(⟨900,1112⟩ : Region).Contains (1112-213) := by decide
''')
    def test_wrong_path_entry_stack_overwrites_callback(self):
        self.succeeds(HEADER+'''
def state : X86Memory.State := ⟨fun _ => 960,fun _ => 0⟩
example : ¬E1M1PathMapSetup.Safe state (1000-44) := by
  intro h
  have overlap := h.1 (1000-44) (by simp [OriginalPathInit.writes,state])
  exact overlap 0 0 rfl
''')
    def test_callback_push_aliases_intercept_record(self):
        self.succeeds(HEADER+'''
example : ¬Apart (OriginalLineCollection.slot 0x2ba20 127 8) (0x2c0a8-140) := by
  unfold Apart; decide
example : ¬Apart (0x2c028#32) (0x2c0b4-140) := by unfold Apart; decide
example : ¬E1M1AimMapRegions.globalStores.Disjoint (⟨0x2c01c,0x2c0a8⟩ : Region) := by decide
''')
    def test_upper_word_bound_and_separation_required(self):
        self.mutations(self.contract('E1M1AimCallbackRegions','above'),[
          ('(high : n≤64)','(high : n≤65)'),
          ('off.toNat≤2^32-68','off.toNat≤2^32-67')])
        self.mutations(self.contract('E1M1AimCallbackRegions','upper_collection'),[
          ('(placement : Doom.Proofs.E1M1AimCallbackRegions.Layout stack lines)','(placement : True)')])
    def test_callback_requires_correct_path_entry_position(self):
        self.mutations(self.contract('E1M1AimCallbackRegions','callback'),[
          ('(position : s.regs 4=q.sp-52)','(position : s.regs 4=q.sp-40)'),
          ('(reserve : E1M1AimWalkRegions.Reserve stack q.sp)','(reserve : True)')])
    def test_complete_query_replaces_only_named_handoff_guards(self):
        decl=proof.declaration('E1M1AimCallbackEntry','execution')
        for name in ['separated','callbackSafe','cursorCall']:self.assertNotIn('('+name+' :',decl)
        for name in ['common','statics','scenes','payloads','room','initial']:self.assertIn('('+name+' :',decl)
        self.mutations(self.contract('E1M1AimCallbackEntry','execution'),[
          ('(placement : E1M1AimCallbackRegions.Layout stack q.lines)','(placement : True)'),
          ('(reserve : E1M1AimWalkRegions.Reserve stack q.sp)','(reserve : True)')])
    def test_pre_ray_view_still_requires_query_stack_position(self):
        self.mutations(self.contract('E1M1AimCallbackEntry','pre_ray'),[
          ('(position : s.regs 4=q.sp-24)','(position : True)')])
    def test_decision_keeps_original_return_word_and_guard(self):
        self.mutations(self.contract('E1M1AimCallbackEntry','decision'),[
          ('(returnSafe : E1M1PathMapQuery.Safe s (s.regs 4))','(returnSafe : True)'),
          ('(resume : (load32 s.memory (s.regs 4)).toNat=if second then 0x2d7f8 else 0x2d7d5)','(resume : True)')])
if __name__=='__main__':unittest.main()

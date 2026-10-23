"""Collection stack, intercept buffer and shared-linedef stamp boundaries."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_catalog_entry as prior
import verify_e1m1_aim_collection_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCollectionEntry\n'+proof.HEADER+'''
set_option maxRecDepth 32768
'''
class AimCollectionEntryTests(unittest.TestCase):
    lean=prior.AimCatalogEntryTests.lean
    succeeds=prior.AimCatalogEntryTests.succeeds
    rejects=prior.AimCatalogEntryTests.rejects
    mutations=prior.AimCatalogEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimCollectionEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_line_pointer_window_ends_at_stamp_boundary(self):
        self.succeeds(HEADER+'''
example : Apart (4096+50 : Word) (OriginalLineVisits.stamp 4096 0) := by
  exact E1M1AimStampRegions.line_field 4096 0 0 50 (by decide) (by decide) (by decide)
example : ¬Apart (4096+51 : Word) (OriginalLineVisits.stamp 4096 0) := by unfold Apart; decide
example : Apart (E1M1ScanGeometry.linePointer 4096 474+50)
    (OriginalLineVisits.stamp 4096 474) :=
  E1M1AimStampRegions.line_field 4096 474 474 50 (by decide) (by decide) (by decide)
''')
    def test_adjacent_linedefs_and_wrapping_base(self):
        self.succeeds(HEADER+'''
example (base : Word) : Apart (E1M1ScanGeometry.linePointer base 1+16)
    (OriginalLineVisits.stamp base 0) :=
  E1M1AimStampRegions.line_field base 1 0 16 (by decide) (by decide) (by decide)
example (base : Word) : Apart (E1M1ScanGeometry.linePointer base 0+50)
    (OriginalLineVisits.stamp base 1) :=
  E1M1AimStampRegions.line_field base 0 1 50 (by decide) (by decide) (by decide)
example : Apart (E1M1ScanGeometry.linePointer 0xfffffff8 0+50)
    (OriginalLineVisits.stamp 0xfffffff8 0) :=
  E1M1AimStampRegions.line_field 0xfffffff8 0 0 50 (by decide) (by decide) (by decide)
''')
    def test_collection_reserve_and_actual_deepest_slot(self):
        self.succeeds(HEADER+'''
example : E1M1AimWalkRegions.Reserve ⟨100,312⟩ 312 := by unfold E1M1AimWalkRegions.Reserve; decide
example : ¬E1M1AimWalkRegions.Reserve ⟨101,312⟩ 312 := by unfold E1M1AimWalkRegions.Reserve; decide
example : ¬E1M1AimWalkRegions.Reserve ⟨0,212⟩ 211 := by unfold E1M1AimWalkRegions.Reserve; decide
example (lines : Word) : ¬E1M1FiringMapState.Safe 312 lines 100 := by
  intro h
  have hit := h.objects.fraction (-40) (by simp)
  exact hit 0 0 (by decide)
''')
    def test_selection_and_callback_return_slot_cannot_alias_read(self):
        self.succeeds(HEADER+'''
example : ¬E1M1AimEntryFrame.SafeWord (312-112) 172 := by
  intro h
  exact h.2.2 0 0 (by decide)
example (s : X86Memory.State) : ¬E1M1AimMapFrame.StableWord s (s.regs 4) := by
  intro h
  exact h.2.2.2 0 0 rfl
''')
    def test_last_intercept_record_and_cursor_are_covered(self):
        self.succeeds(HEADER+'''
example : OriginalLineCollection.slot 0x2ba20 127 8=0x2c01c := by decide
example : E1M1AimMapRegions.globalStores.Contains
    (OriginalLineCollection.slot 0x2ba20 127 8) := by decide
example : E1M1AimMapRegions.globalStores.Contains 0x2c028 := by decide
example (stack : Region) : ¬E1M1AimObjectRegions.Located stack 0x2c01c := by
  rintro ⟨r,inside,_,disjoint⟩
  have hit := E1M1NoiseAllocation.Region.apart inside
    (by decide : E1M1AimMapRegions.globalStores.Contains 0x2c01c) disjoint
  exact hit 0 0 rfl
''')
    def test_line_field_proof_retains_field_and_index_bounds(self):
        self.mutations(self.contract('E1M1AimStampRegions','line_field'),[
            ('(fits : off+4 ≤ 54)','(fits : off+4 ≤ 55)'),
            ('(hi : i<475)','(hi : True)'),
            ('(hj : j<475)','(hj : True)')])
    def test_collection_guard_cannot_drop_stamp_separation(self):
        self.mutations(self.contract('E1M1AimWalkRegions','collection'),[
            ('(stamps : ∀ j<475, Apart a (OriginalLineVisits.stamp lines j))','(stamps : True)'),
            ('(reserve : Doom.Proofs.E1M1AimWalkRegions.Reserve stack sp)','(reserve : True)')])
    def test_ordered_frame_requires_real_frame_and_bounded_record(self):
        self.mutations(self.contract('E1M1AimCollectionEntry','word'),[
            ('(frame : E1M1AimHistoryCycle.Frame (E1M1AimQueryCatalog.view q s) out)','(frame : True)'),
            ('(bounded : marked<128)','(bounded : True)'),
            ('(pointer : (E1M1AimQueryCatalog.view q s).regs 3=E1M1MinimumScan.address marked)','(pointer : True)')])
    def test_catalog_join_derives_later_instead_of_assuming_it(self):
        for name in ['initial','remaining','controller']:
            decl=proof.declaration('E1M1AimCollectionEntry',name)
            self.assertNotIn('(later :',decl)
            self.assertIn('E1M1AimStampRegions.Layout',decl)
            self.assertIn('E1M1AimWalkRegions.Reserve',decl)
        self.mutations(self.contract('E1M1AimCollectionEntry','initial'),[
            ('(placement : E1M1AimStampRegions.Layout stack q.lines hits (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) portals)','(placement : True)'),
            ('(walkReserve : E1M1AimWalkRegions.Reserve stack q.sp)','(walkReserve : True)')])
    def test_controller_keeps_other_inputs_and_original_angle(self):
        self.mutations(self.contract('E1M1AimCollectionEntry','controller'),[
            ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
            ('(other : Doom.Proofs.E1M1AimCatalogEntry.OtherInputs q (E1M1AimControllerInputs.layout s angle) scene shooter hits portals walls who)','(other : True)')])
if __name__=='__main__':unittest.main()

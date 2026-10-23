"""Derived callback layout, buffer boundaries and retained execution/content contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_global_entry as prior
import verify_e1m1_aim_helper_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimHelperEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimHelperEntryTests(unittest.TestCase):
    lean=prior.AimGlobalEntryTests.lean
    succeeds=prior.AimGlobalEntryTests.succeeds
    rejects=prior.AimGlobalEntryTests.rejects
    mutations=prior.AimGlobalEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimHelperEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_concrete_full_layout_at_empty_and_full_capacity(self):
        self.succeeds(HEADER+'''
def callback : X86Memory.State := ⟨fun _ => 972,fun _ => 0⟩
example (q : E1M1CellWalkInvariant.Context) (anchor : q.sp=1112) (lines : q.lines=4096)
    (hits : Array Intercept) (capacity : hits.size≤128) :
    E1M1AimCycleInvariant.Layout callback hits := by
  apply E1M1AimHelperRegions.layout ⟨900,1112⟩ q callback hits
  · simpa only [lines] using (show E1M1AimGlobalRegions.Layout ⟨900,1112⟩ 4096 from
      ⟨⟨by decide,by decide,by decide⟩,by decide⟩)
  · simp only [anchor,E1M1AimWalkRegions.Reserve]; decide
  · simp [callback,anchor]
  · exact capacity
example : (#[] : Array Intercept).size≤128 := by decide
example (hit : Intercept) : (Array.replicate 128 hit).size≤128 := by simp
''')
    def test_four_byte_boundary_and_last_record(self):
        self.succeeds(HEADER+'''
example : E1M1AimHelperRegions.recordArea.Contains (0x2c028#32) := by decide
example : ¬E1M1AimHelperRegions.recordArea.Contains (0x2c029#32) := by decide
example : ¬E1M1AimHelperRegions.recordArea.Contains (0x2c02c#32) := by decide
example : E1M1AimCellWalk.buffer.Contains (OriginalLineCollection.slot 0x2ba20 127 8) :=
  E1M1AimCellWalk.buffer_word 127 (by decide) 8 (by simp)
example : ¬E1M1AimCellWalk.buffer.Contains (OriginalLineCollection.slot 0x2ba20 128 0) := by decide
''')
    def test_unbounded_records_can_alias_opening_store(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (hits : Array Intercept) (large : 129<hits.size) :
    ¬E1M1AimRecordFrame.RecordsSafe s hits := by
  intro safe
  have word : E1M1AimRecordFrame.ReadSafe s 0x2c02c := by
    simpa [E1M1MinimumScan.address] using safe 129 large 0 (by simp)
  exact word.2 _ (by simp [E1M1AimReturnFrame.writes,E1M1NoiseLineProgress.openingGlobals]) 0 0 rfl
''')
    def test_callback_read_frame_does_not_hide_parent_stores(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) : ¬E1M1AimMapFrame.StableWord s 0x2c028 := by
  intro h
  exact h.2.2.1 0 0 rfl
example (s : X86Memory.State) : ¬E1M1AimMapFrame.StableWord s (E1M1MinimumScan.address 0) := by
  intro h
  exact h.2.1 0 (by decide) 0 0 rfl
''')
    def test_layout_retains_capacity_reserve_and_position(self):
        self.mutations(self.contract('E1M1AimHelperRegions','layout'),[
          ('(capacity : hits.size≤128)','(capacity : True)'),
          ('(reserve : E1M1AimWalkRegions.Reserve stack q.sp)','(reserve : True)'),
          ('(position : s.regs 4=q.sp-140)','(position : s.regs 4=q.sp-136)')])
    def test_opening_and_return_reads_keep_separation(self):
        self.mutations(self.contract('E1M1AimHelperRegions','opening_reads'),[
          ('(fixed : ∀ b∈E1M1NoiseLineProgress.openingGlobals, Apart a b)','(fixed : True)')])
        self.mutations(self.contract('E1M1AimHelperRegions','return_safe'),[
          ('(placement : Doom.Proofs.E1M1AimGlobalRegions.Layout stack q.lines)','(placement : True)')])
    def test_actual_callback_transport_retains_input_and_memory_image(self):
        self.mutations(self.contract('E1M1AimHelperRegions','callback_records'),[
          ('(input : E1M1AimMapped.Inputs s hit line front back ff fc bf bc)','(input : True)'),
          ('(image : OriginalLineFinish.Encodes s.memory 0x2ba20 lookup hits)','(image : True)')])
    def test_residual_fields_remove_only_layout(self):
        def fields(module):
            s=(ROOT/f'Doom/Proofs/{module}.lean').read_text().split('structure OtherInputs',1)[1].split('\n\n',1)[0]
            return re.findall(r'^  (\w+) :',s,re.M)
        self.assertEqual(fields('E1M1AimHelperEntry'),[x for x in fields('E1M1AimGlobalEntry') if x!='layout'])
        self.assertEqual(fields('E1M1AimHelperEntry'),['portals','shooterReg','actors','walls'])
        self.mutations(self.contract('E1M1AimHelperEntry','other'),[
          ('(input : Doom.Proofs.E1M1AimHelperEntry.OtherInputs q s scene shooter hits portals walls who)','(input : True)')])
    def test_catalog_joins_keep_capacity_and_original_angle(self):
        self.mutations(self.contract('E1M1AimHelperEntry','initial'),[
          ('(capacity : hits.size≤128)','(capacity : True)')])
        self.mutations(self.contract('E1M1AimHelperEntry','controller'),[
          ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
          ('(position : s.regs 4=q.sp-4)','(position : s.regs 4=q.sp-24)')])
if __name__=='__main__':unittest.main()

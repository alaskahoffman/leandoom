"""Range boundaries and contract regressions for conditional aiming entry guards."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_original_inputs as prior
import verify_e1m1_aim_allocated_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimAllocatedEntry\n'+proof.HEADER+'''
set_option maxRecDepth 32768
'''
class AimAllocatedEntryTests(unittest.TestCase):
    lean=prior.AimOriginalInputsTests.lean
    succeeds=prior.AimOriginalInputsTests.succeeds
    rejects=prior.AimOriginalInputsTests.rejects
    mutations=prior.AimOriginalInputsTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimAllocatedEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_twenty_byte_reserve_and_wrap_boundary(self):
        self.succeeds(HEADER+'''
def state (sp : Word) : X86Memory.State := ⟨fun _ => sp, fun _ => 0⟩
example : E1M1AimRegions.StackReserve ⟨100,120⟩ (state 120) := by unfold E1M1AimRegions.StackReserve; decide
example : ¬E1M1AimRegions.StackReserve ⟨101,120⟩ (state 120) := by unfold E1M1AimRegions.StackReserve; decide
example : E1M1AimRegions.StackReserve ⟨0,20⟩ (state 20) := by unfold E1M1AimRegions.StackReserve; decide
example : ¬E1M1AimRegions.StackReserve ⟨0,20⟩ (state 19) := by unfold E1M1AimRegions.StackReserve; decide
example : ¬E1M1AimRegions.StackReserve ⟨0,4294967297⟩ (state 120) := by unfold E1M1AimRegions.StackReserve; decide
example : (⟨100,120⟩ : Region).Contains (100#32) := by decide
example : ¬(⟨100,120⟩ : Region).Contains (99#32) := by decide
''')
    def test_adjacent_regions_allowed_but_one_byte_overlap_rejected(self):
        self.succeeds(HEADER+'''
example : (⟨96,100⟩ : Region).Disjoint ⟨100,120⟩ := by decide
example : Apart (96#32) (100#32) := by unfold Apart; decide
example : ¬(⟨97,101⟩ : Region).Disjoint ⟨100,120⟩ := by decide
example : ¬Apart (97#32) (100#32) := by unfold Apart; decide
example : (⟨120,124⟩ : Region).Disjoint ⟨100,120⟩ := by decide
example : ¬(⟨119,123⟩ : Region).Disjoint ⟨100,120⟩ := by decide
''')
    def test_blockmap_last_halfword_needs_two_byte_guard_extension(self):
        self.succeeds(HEADER+'''
example : (E1M1AimStaticRegions.blockmap 4096).Contains (4096+2*3460) := by decide
example : ¬(⟨4096,4096+6922⟩ : Region).Contains (4096+2*3460) := by decide
example : ¬(E1M1AimStaticRegions.blockmap 4096).Contains (4096+2*3461) := by decide
example : (E1M1AimStaticRegions.blockmap (4294967296-6924)).Contains
    (4294967296-4) := by decide
example : ¬(E1M1AimStaticRegions.blockmap (4294967296-6923)).Contains
    (4294967296-4) := by decide
''')
    def test_stamp_stride_and_last_table_entry(self):
        self.succeeds(HEADER+'''
example : (E1M1AimStaticRegions.linedefs 4096).Contains
    (OriginalLineVisits.stamp 4096 474) := by decide
example : ¬(E1M1AimStaticRegions.linedefs 4096).Contains
    (OriginalLineVisits.stamp 4096 475) := by decide
example : (0x5a84#32)+BitVec.ofNat 32 (10239*4)=0xfa80 := by decide
example : ∀ a∈E1M1AimRetryGeometry.sampleReads ⟨0xffffffff⟩,
    E1M1AimStaticRegions.globals.Contains a := E1M1AimStaticRegions.sample_words _
''')
    def test_region_coverage_and_stack_reserve_cannot_be_dropped(self):
        self.mutations(self.contract('E1M1AimRegions','safe_reads'),[
            ('(reserve : Doom.Proofs.E1M1AimRegions.StackReserve stack s)','(reserve : True)'),
            ('(covered : Doom.Proofs.E1M1AimRegions.Covered stack addresses)','(covered : True)')])
    def test_setup_requires_pinned_counts_and_layout(self):
        self.mutations(self.contract('E1M1AimAllocatedEntry','setup_safe'),[
            ('(words : q.words.size=3461)','(words : True)'),
            ('(lines : q.world.lines.size=475)','(lines : True)'),
            ('(placement : Doom.Proofs.E1M1AimStaticRegions.Layout stack q.base q.lines (s.regs 0))','(placement : True)')])
    def test_entry_still_requires_memory_contents_and_original_angle(self):
        self.mutations(self.contract('E1M1AimAllocatedEntry','inputs'),[
            ('(before : E1M1AimSetupEntry.Inputs q (Doom.Proofs.E1M1AimControllerInputs.layout s angle) thing angle (Fixed.ofInt 1024))','(before : True)'),
            ('(tables : ThrustTables s.memory)','(tables : True)'),
            ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)')])
    def test_freshness_is_preserved_not_created(self):
        self.mutations(self.contract('E1M1AimAllocatedEntry','fresh'),[
            ('(before : E1M1AimStampImage.Fresh s.memory lines epoch 475)','(before : True)'),
            ('core.memory lines epoch 475 :=','core.memory lines (epoch+1) 475 :=')])
    def test_nonwrapping_field_and_index_bounds_are_required(self):
        self.mutations(self.contract('E1M1AimStaticRegions','map_word'),[
            ('(bound : base.toNat+6924 ≤ 2^32)','(bound : True)'),
            ('(hi : i<3461)','(hi : True)')])
if __name__=='__main__':unittest.main()

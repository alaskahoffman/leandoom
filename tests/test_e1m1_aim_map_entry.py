"""Check setup-stack boundaries, fixed-store aliasing and map-entry contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_allocated_entry as prior
import verify_e1m1_aim_map_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimMapEntry\n'+proof.HEADER+'''
set_option maxRecDepth 32768
'''
class AimMapEntryTests(unittest.TestCase):
    lean=prior.AimAllocatedEntryTests.lean
    succeeds=prior.AimAllocatedEntryTests.succeeds
    rejects=prior.AimAllocatedEntryTests.rejects
    mutations=prior.AimAllocatedEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimMapEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_exact_setup_reserve_and_controller_offset(self):
        self.succeeds(HEADER+'''
def state (sp : Word) : X86Memory.State := ⟨fun _ => sp, fun _ => 0⟩
example : E1M1AimSetupFootprint.Reserve ⟨100,204⟩ (state 204) := by
  unfold E1M1AimSetupFootprint.Reserve; decide
example : ¬E1M1AimSetupFootprint.Reserve ⟨101,204⟩ (state 204) := by
  unfold E1M1AimSetupFootprint.Reserve; decide
example : E1M1AimSetupFootprint.Reserve ⟨100,224⟩
    (E1M1AimControllerInputs.layout (state 224) ⟨0⟩) := by
  unfold E1M1AimSetupFootprint.Reserve; decide
example : ¬E1M1AimSetupFootprint.Reserve ⟨100,224⟩
    (E1M1AimControllerInputs.layout (state 223) ⟨0⟩) := by
  unfold E1M1AimSetupFootprint.Reserve; decide
example : ¬E1M1AimSetupFootprint.Reserve ⟨0,104⟩ (state 103) := by
  unfold E1M1AimSetupFootprint.Reserve; decide
''')
    def test_actual_deepest_helper_slot_must_be_protected(self):
        self.succeeds(HEADER+'''
def state : X86Memory.State := ⟨fun _ => 204, fun _ => 0⟩
example : ¬E1M1PathMapQuery.Safe state 100 := by
  intro h
  have hit := h.later.2 (-16) (by simp [E1M1PathMapSetup.offsets])
  exact hit 0 0 (by decide)
example : 100#32∈E1M1AimSetupFootprint.writes state := by
  simp [E1M1AimSetupFootprint.writes,E1M1AimSetupFootprint.offsets,state]
''')
    def test_epoch_is_written_not_implicitly_preserved(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) : ¬E1M1PathMapQuery.Safe s 0x13580 := by
  intro h
  have hit := h.later.1 0x13580 (by simp [OriginalPathInit.writes])
  exact hit 0 0 rfl
example : ¬(E1M1AimStaticRegions.blockmap 0x13580).Disjoint
    E1M1AimMapRegions.globalStores := by decide
''')
    def test_global_store_boundary_is_byte_precise(self):
        self.succeeds(HEADER+'''
example : (E1M1AimStaticRegions.blockmap 0x2c1ec).Disjoint
    E1M1AimMapRegions.globalStores := by decide
example : ¬(E1M1AimStaticRegions.blockmap 0x2c1eb).Disjoint
    E1M1AimMapRegions.globalStores := by decide
example : Apart (0x2c1ec#32) (0x2c1e8#32) := by unfold Apart; decide
example : ¬Apart (0x2c1eb#32) (0x2c1e8#32) := by unfold Apart; decide
''')
    def test_region_guard_cannot_drop_fixed_store_protection(self):
        self.mutations(self.contract('E1M1AimSetupFootprint','region_safe'),[
            ('(fixed : ∀ b∈Doom.Proofs.E1M1AimSetupFootprint.globals, Apart a b)','(fixed : True)'),
            ('(separate : region.Disjoint stack)','(separate : True)'),
            ('(reserve : Doom.Proofs.E1M1AimSetupFootprint.Reserve stack s)','(reserve : True)')])
    def test_map_constructor_requires_values_size_and_placement(self):
        self.mutations(self.contract('E1M1AimMapEntry','inputs'),[
            ('(values : Doom.Proofs.E1M1AimMapEntry.Values s.memory base lines words)','(values : True)'),
            ('(size : words.size=3461)','(size : True)'),
            ('(placement : Doom.Proofs.E1M1AimMapRegions.Layout stack base)','(placement : True)')])
    def test_query_execution_keeps_actual_entry_and_map_dimensions(self):
        self.mutations(self.contract('E1M1AimMapEntry','execution'),[
            ('⟨s,f,0x2bb80⟩','⟨s,f,0x2c8a0⟩'),
            ('words 36 23 :=','words 23 36 :='),
            ('[] 36\n','[] 35\n')])
    def test_controller_requires_full_setup_reserve(self):
        self.mutations(self.contract('E1M1AimMapEntry','controller_map'),[
            ('(room : stack.lo+124 ≤ (s.regs 4).toNat)','(room : stack.lo+123 ≤ (s.regs 4).toNat)'),
            ('(bound : stack.hi ≤ 2^32)','(bound : True)'),
            ('(values : Doom.Proofs.E1M1AimMapEntry.Values s.memory base lines words)','(values : True)')])
    def test_values_contract_contains_no_protection_assumptions(self):
        text=(ROOT/'Doom/Proofs/E1M1AimMapEntry.lean').read_text()
        fields=text.split('structure Values ',1)[1].split('/--',1)[0]
        self.assertEqual(re.findall(r'^  (\w+) :',fields,re.M),['width','height','table','lists','lines','image'])
        for hidden in ['Safe','Apart','Reserve','Layout','entry','traversal']:
            self.assertNotIn(hidden,fields)
if __name__=='__main__':unittest.main()

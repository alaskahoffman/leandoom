"""Pinned cell bounds, byte windows and actual controller-to-setup payload transport."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_collection_entry as prior
import verify_e1m1_aim_cell_entry as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCellEntry\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimCellEntryTests(unittest.TestCase):
    lean=prior.AimCollectionEntryTests.lean
    succeeds=prior.AimCollectionEntryTests.succeeds
    rejects=prior.AimCollectionEntryTests.rejects
    mutations=prior.AimCollectionEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimCellEntry.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_signed_grid_edges_and_last_index(self):
        self.succeeds(HEADER+'''
example : Collision.pathCellIndex 35 22 36=827 := by decide
example : Collision.pathCellInside 35 22 36 23=true := by decide
example : Collision.pathCellInside (-1) 0 36 23=false := by decide
example : Collision.pathCellInside 0 (-1) 36 23=false := by decide
example : Collision.pathCellInside 36 0 36 23=false := by decide
example : Collision.pathCellInside 0 23 36 23=false := by decide
example : Collision.pathCellIndex 35 22 36<828 :=
  E1M1AimCellRegions.index_bound 35 22 (by decide)
''')
    def test_head_table_last_word_requires_all_four_bytes(self):
        self.succeeds(HEADER+'''
example : E1M1CellObjectSelection.address 4096 35 22 36=7404 := by decide
example : (E1M1AimObjectRegions.region 4096 3312).Contains 7404 := by decide
example : ¬(E1M1AimObjectRegions.region 4096 3311).Contains 7404 := by decide
example : ¬(E1M1AimObjectRegions.region 4096 3312).Contains
    (E1M1CellObjectSelection.address 4096 0 23 36) := by decide
example : E1M1CellObjectSelection.address 0xfffffff0 35 22 36=3292 := by decide
example : ¬(E1M1AimObjectRegions.region 0xfffffff0 3312).Contains 3292 := by decide
''')
    def test_actor_radius_and_vertex_windows(self):
        self.succeeds(HEADER+'''
example : (E1M1AimObjectRegions.region 4097 68).Contains (4097+64) := by decide
example : ¬(E1M1AimObjectRegions.region 4097 67).Contains (4097+64) := by decide
example : (E1M1AimObjectRegions.region 4097 68).Contains (4097+44) := by decide
example : (E1M1AimObjectRegions.region 4097 8).Contains (4097+4) := by decide
example : ¬(E1M1AimObjectRegions.region 4097 7).Contains (4097+4) := by decide
''')
    def test_global_pointer_inside_envelope_but_avoids_actual_stores(self):
        self.succeeds(HEADER+'''
example : E1M1AimMapRegions.globalStores.Contains 0x2c0f8 := by decide
example : ∀ b∈E1M1AimSetupFootprint.globals, Apart (0x2c0f8#32) b :=
  E1M1AimCellEntry.global_apart
example (s : X86Memory.State) : ¬E1M1PathMapQuery.Safe s 0x2c028 := by
  intro h
  have hit := h.later.1 0x2c028 (by simp [OriginalPathInit.writes])
  exact hit 0 0 rfl
''')
    def test_bounds_cannot_be_removed(self):
        self.mutations(self.contract('E1M1AimCellRegions','index_bound'),[
          ('(inside : Collision.pathCellInside x y 36 23=true)','(inside : True)')])
        self.mutations(self.contract('E1M1AimCellRegions','line_located'),[
          ('(bounded : i<475)','(bounded : i≤475)'),
          ('(fits : off+4≤54)','(fits : True)')])
    def test_head_protection_requires_storage_and_signed_guard(self):
        self.mutations(self.contract('E1M1AimCellRegions','head_located'),[
          ('(storage : Doom.Proofs.E1M1AimObjectRegions.Storage stack links 3312)','(storage : True)'),
          ('(inside : Collision.pathCellInside x y 36 23=true)','(inside : True)')])
    def test_payload_setup_requires_placement_and_stack(self):
        self.mutations(self.contract('E1M1AimCellEntry','safe'),[
          ('(placement : Doom.Proofs.E1M1AimCellRegions.Layout stack q c)','(placement : True)'),
          ('(reserve : E1M1AimSetupFootprint.Reserve stack s)','(reserve : True)')])
    def test_transport_requires_initial_values(self):
        self.mutations(self.contract('E1M1AimCellEntry','traversal'),[
          ('(before : E1M1QueryImages.Payload s.memory q c)','(before : True)')])
    def test_controller_requires_original_angle_and_room(self):
        self.mutations(self.contract('E1M1AimCellEntry','controller'),[
          ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
          ('(room : stack.lo+124≤(s.regs 4).toNat)','(room : stack.lo+123≤(s.regs 4).toNat)'),
          ('(before : E1M1QueryImages.Payload s.memory q c)','(before : True)')])
if __name__=='__main__':unittest.main()

"""Stamp aliasing, collection globals and region-derived future-cell transport."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_cell_entry as prior
import verify_e1m1_aim_cell_collection as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimCellCollection\n'+proof.HEADER+'\nset_option maxRecDepth 32768\n'
class AimCellCollectionTests(unittest.TestCase):
    lean=prior.AimCellEntryTests.lean
    succeeds=prior.AimCellEntryTests.succeeds
    rejects=prior.AimCellEntryTests.rejects
    mutations=prior.AimCellEntryTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimCellCollection.pinned_map_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_vertex_and_actor_stamp_aliases_rejected(self):
        self.succeeds(HEADER+'''
example : ¬Apart (4150#32) (OriginalLineVisits.stamp 4096 0) := by unfold Apart; decide
example : ¬(E1M1AimObjectRegions.region 4146 8).Disjoint (E1M1AimStaticRegions.linedefs 4096) := by decide
example : ¬Apart (4086+64 : Word) (OriginalLineVisits.stamp 4096 0) := by unfold Apart; decide
example : ¬(E1M1AimObjectRegions.region 4086 68).Disjoint (E1M1AimStaticRegions.linedefs 4096) := by decide
example : Apart (4096+50 : Word) (OriginalLineVisits.stamp 4096 0) :=
  E1M1AimStampRegions.line_field 4096 0 0 50 (by decide) (by decide) (by decide)
''')
    def test_head_table_cannot_overlap_stamps(self):
        self.succeeds(HEADER+'''
example : E1M1CellObjectSelection.address 842 35 22 36=4150 := by decide
example : ¬Apart (E1M1CellObjectSelection.address 842 35 22 36)
    (OriginalLineVisits.stamp 4096 0) := by unfold Apart; decide
example : ¬(E1M1AimObjectRegions.region 842 3312).Disjoint (E1M1AimStaticRegions.linedefs 4096) := by decide
''')
    def test_collection_buffer_exact_boundaries(self):
        self.succeeds(HEADER+'''
example : E1M1AimCellWalk.buffer.Contains (OriginalLineCollection.slot 0x2ba20 127 8) :=
  E1M1AimCellWalk.buffer_word 127 (by decide) 8 (by simp)
example : ¬E1M1AimCellWalk.buffer.Contains (OriginalLineCollection.slot 0x2ba20 128 0) := by decide
example : Apart (0x2ba1c#32) (0x2ba20#32) := by unfold Apart; decide
example : ¬Apart (0x2ba1d#32) (0x2ba20#32) := by unfold Apart; decide
example : Apart (0x2c024#32) (0x2c028#32) := by unfold Apart; decide
''')
    def test_initialized_globals_are_not_preserved_during_setup(self):
        self.succeeds(HEADER+'''
example : OriginalLineMixedInvariant.ArraySafe 0x2ba20 0x2ba10 :=
  E1M1AimCellWalk.global_array 0x2ba10 (by simp [E1M1AimCellWalk.globals])
example : OriginalLineMixedInvariant.ArraySafe 0x2ba20 0x2c024 :=
  E1M1AimCellWalk.global_array 0x2c024 (by simp [E1M1AimCellWalk.globals])
example (s : X86Memory.State) : ¬E1M1PathMapQuery.Safe s 0x2ba10 := by
  intro h
  exact (h.later.1 _ (by simp [OriginalPathInit.writes])) 0 0 rfl
example (s : X86Memory.State) : ¬E1M1PathMapQuery.Safe s 0x2c024 := by
  intro h
  exact (h.later.1 _ (by simp [OriginalPathInit.writes])) 0 0 rfl
''')
    def test_phase_guard_requires_all_three_write_classes(self):
        self.mutations(self.contract('E1M1AimCellWalk','word'),[
          ('(separate : r.Disjoint stack)','(separate : True)'),
          ('(array : OriginalLineMixedInvariant.ArraySafe 0x2ba20 a)','(array : True)'),
          ('(stamps : ∀ j<475, Apart a (OriginalLineVisits.stamp lines j))','(stamps : True)')])
    def test_stamp_proof_requires_external_region_separation(self):
        self.mutations(self.contract('E1M1AimCellStamps','reads'),[
          ('(placement : Doom.Proofs.E1M1AimCellStamps.Layout stack q c)',
           '(placement : E1M1AimCellRegions.Layout stack q c)')])
    def test_future_images_keep_execution_frame_and_initial_images(self):
        self.mutations(self.contract('E1M1AimCellCollection','images'),[
          ('(frame : E1M1CellMapInvariant.Frame q.sp q.lines m n)','(frame : True)'),
          ('(before : E1M1CellWalkInvariant.Images q cells m)','(before : True)')])
        decl=proof.declaration('E1M1AimCellCollection','images')
        self.assertNotIn('E1M1CellWalkInvariant.Static',decl)
    def test_actual_lookup_keeps_numeric_contracts_and_scan_pointers(self):
        self.mutations(self.contract('E1M1AimCellCollection','lookup_ready'),[
          ('(contracts : E1M1CellSceneInvariant.Contracts q.sp q.lines q.trace c.cell c.data q.objects c.nodes)',
           '(contracts : True)'),
          ('(items : E1M1PathMapLookup.ScanWords (E1M1PathMapCaller.scan s).core q.lines c.cell)',
           '(items : True)')])
    def test_setup_collection_join_keeps_original_payload_and_frame(self):
        self.mutations(self.contract('E1M1AimCellCollection','setup_then_collection'),[
          ('(before : E1M1QueryImages.Payload s.memory q c)','(before : True)'),
          ('(frame : E1M1CellMapInvariant.Frame q.sp q.lines (E1M1PathMapQuery.traversal s).core.memory n)',
           '(frame : True)')])
if __name__=='__main__':unittest.main()

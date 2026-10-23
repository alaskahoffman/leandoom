"""Check exact stamp history through cells, grid steps and mixed itineraries."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_stamp_next_scan as prior
import verify_e1m1_aim_stamp_walk as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimStampWalk\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight BitVec.add
'''
class AimStampWalkTests(unittest.TestCase):
    lean=prior.AimStampNextScanTests.lean
    succeeds=prior.AimStampNextScanTests.succeeds
    rejects=prior.AimStampNextScanTests.rejects
    mutations=prior.AimStampNextScanTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimStampWalk.from_entry_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_object_frame_uses_only_its_own_write_guards(self):
        source=self.contract('E1M1AimStampCellTail','object_run')
        self.assertIn('∀ a, Doom.Proofs.E1M1FiringVisitedNext.TailSafe sp a →',source)
        self.mutations(source,[
            ('∀ a, Doom.Proofs.E1M1FiringVisitedNext.TailSafe sp a →','∀ a, True →'),
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : True)')])
    def test_grid_step_preserves_origin_epoch_and_visited_array(self):
        self.mutations(self.contract('E1M1AimStampCellTail','advance'),[
            ('(image : E1M1AimStampImage.Image origin s.core.memory lines epoch seen)','(image : True)'),
            ('E1M1AimStampImage.Image origin out.core.memory lines epoch seen',
             'E1M1AimStampImage.Image origin out.core.memory lines (epoch+1) seen'),
            ('(stampSafe : ∀ j<seen.size, Doom.Proofs.E1M1FiringVisitedNext.TailSafe sp (Doom.Proofs.OriginalLineVisits.stamp lines j))',
             '(stampSafe : True)')])
    def test_line_scan_history_is_not_reset_before_objects(self):
        self.mutations(self.contract('E1M1AimStampCell','scan'),[
            ('Doom.Proofs.OriginalLineVisits.markPrefix (Doom.Proofs.E1M1ScanContracts.candidates trace lines cell.ids data) cell.ids.length 0 seen',
             'Doom.Proofs.OriginalLineVisits.markPrefix (Doom.Proofs.E1M1ScanContracts.candidates trace lines cell.ids data) cell.ids.length 0 (Array.replicate 475 false)'),
            ('(represented : Doom.Proofs.OriginalLineVisits.Represents s.core.memory lines epoch seen)','(represented : True)')])
    def test_lookup_requires_the_initial_map_cell_and_stamp_guards(self):
        self.mutations(self.contract('E1M1AimStampCell','gate'),[
            ('(valid : cell.Valid words)','(valid : True)'),
            ('(epochSafe : Doom.Proofs.E1M1FiringVisitedNext.TailSafe sp (0x13580#32))','(epochSafe : True)'),
            ('(image : E1M1AimStampImage.Image origin s.core.memory lines epoch seen)','(image : True)')])
    def test_outside_cell_preserves_history_without_marking(self):
        self.mutations(self.contract('E1M1AimStampWalk','outside'),[
            ('(outMap : Collision.pathCellInside x y q.width q.height=false)',
             '(outMap : Collision.pathCellInside x y q.width q.height=true)'),
            ('E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch seen',
             'E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (Array.replicate 475 false)')])
    def test_mixed_cell_uses_the_real_path_and_actual_images(self):
        self.mutations(self.contract('E1M1AimStampWalk','one'),[
            ('(static : Doom.Proofs.E1M1MixedCellWalk.Admitted q c)','(static : True)'),
            ('(room : r.collected.size+Doom.Proofs.E1M1MixedCellWalk.cost q c≤128)','(room : True)'),
            ('(images : Doom.Proofs.E1M1MixedCellWalk.Images q [c] s.core.memory)','(images : True)')])
    def test_itinerary_composes_history_and_requires_continuation(self):
        self.mutations(self.contract('E1M1AimStampWalk','execution'),[
            ('(follows : Doom.Proofs.E1M1CellWalk.Follows (E1M1PathAdvance.observe s.core) cells)','(follows : True)'),
            ('E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (Doom.Proofs.E1M1MixedCellWalk.history q seen cells)',
             'E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch seen'),
            ('(entry : cells≠[] → s.pc=0x2ca7f)','(entry : True)')])
    def test_entry_specialization_joins_authenticated_program_and_future_freshness(self):
        source=self.contract('E1M1AimStampWalk','from_entry')
        args=source.split(' :\n    ∃ out after')[0]
        self.assertNotIn('(image :',args);self.assertNotIn('(origin :',args)
        self.assertIn('X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program',source)
        self.mutations(source,[
            ('E1M1AimStampImage.Fresh s.core.memory q.lines (q.epoch+1) 475 →',
             'E1M1AimStampImage.Fresh s.core.memory q.lines q.epoch 475 →'),
            ('(room : r.collected.size+Doom.Proofs.E1M1MixedCellWalk.budget q cells≤128)','(room : True)')])
if __name__=='__main__':unittest.main()

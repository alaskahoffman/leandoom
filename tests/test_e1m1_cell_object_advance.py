"""The reusable object phase must follow real selection, list execution and advancement."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_scene as prior
import verify_e1m1_cell_object_advance as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextScene','import Doom.Proofs.E1M1CellObjectAdvance')
RUN='s sp base lines epoch words w h objects trace cell data nodes r seen pc success stack maps mapLayout payload payloadSafe contracts x y mapX mapY inMap links selection selectionSafe tracked capacity represented returns epochSafe stampSafe locals'
ADVANCE=RUN+' world dimension ids scene'

class CellObjectAdvanceTests(unittest.TestCase):
    lean=prior.FiringNextSceneTests.lean
    succeeds=prior.FiringNextSceneTests.succeeds
    rejects=prior.FiringNextSceneTests.rejects
    mutations=prior.FiringNextSceneTests.mutations

    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('CellObjectSelection.transport','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_selection_transport_requires_actual_table_and_head(self):
        self.mutations(self.contract('E1M1CellObjectSelection','transport','m n sp lines links x y width nodes image safe frame'),[
            ('(image : Image m links x y width nodes)','(image : True)'),
            ('(safe : Protected sp lines links x y width)','(safe : True)'),
            ('(frame : E1M1CellMapInvariant.Frame sp lines m n)','(frame : True)')])

    def test_lookup_words_require_both_store_protections(self):
        self.mutations(self.contract('E1M1CellObjectSelection','read_word','s sp stack a callSafe entrySafe'),[
            ('(callSafe : Apart a (sp-(116#32)))','(callSafe : True)'),
            ('(entrySafe : Apart a (sp-(120#32)))','(entrySafe : True)')])
        self.mutations(self.contract('E1M1CellObjectSelection','frame','s sp lines stack'),[
            ('(stack : s.core.regs 4=sp-(112#32))','(stack : True)')])

    def test_lookup_numeric_view_uses_restored_caller_stack(self):
        self.mutations(self.contract('E1M1CellObjectSelection','observe','s sp stack'),[
            ('(stack : s.core.regs 4=sp-(112#32))','(stack : True)'),
            ('(E1M1ObjectBoundary.callerView (result s) sp)',
             '(E1M1ObjectBoundary.callerView (result s) (sp+(4#32)))')])

    def test_lookup_return_word_is_created_at_the_actual_slot(self):
        self.mutations(self.contract('E1M1CellObjectSelection','caller_word','s sp stack'),[
            ('memory (sp-(116#32))=(0x2cab1#32)','memory (sp-(120#32))=(0x2cab1#32)'),
            ('=(0x2cab1#32) :=','=(0x2ca94#32) :=')])

    def test_object_execution_requires_real_selection_capacity_and_entry(self):
        self.mutations(self.contract('E1M1CellObjectRun','execution',RUN),[
            ('(selection : E1M1CellObjectSelection.Image s.core.memory links x y w nodes)','(selection : True)'),
            ('(selectionSafe : E1M1CellObjectSelection.Protected sp lines links x y w)','(selectionSafe : True)'),
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : r.collected.size≤128)'),
            ('(pc : s.pc=0x2ca94)','(pc : True)')])

    def test_object_callbacks_require_persistent_geometry_and_static_layout(self):
        self.mutations(self.contract('E1M1CellObjectRun','execution',RUN),[
            ('(payload : E1M1CellSceneInvariant.Image s.core.memory lines trace cell data nodes)','(payload : True)'),
            ('(payloadSafe : E1M1CellSceneInvariant.Protected sp lines cell data nodes)','(payloadSafe : True)'),
            ('(contracts : E1M1CellSceneInvariant.Contracts sp lines trace cell data objects nodes)','(contracts : True)'),
            ('n≤31+230*nodes.length','n≤30+230*nodes.length')])

    def test_advance_retains_original_step_pc_and_exact_available_reserve(self):
        self.mutations(self.contract('E1M1CellObjectAdvance','execution',ADVANCE),[
            ('E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core)',
             'E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core'),
            ('out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core)','out.pc=0x2ca7f'),
            ('after.collected (128-(r.collected.size+nodes.length))','after.collected (129-(r.collected.size+nodes.length))'),
            ('n≤52+230*nodes.length','n≤51+230*nodes.length')])

    def test_production_scene_claim_needs_id_order_and_targets(self):
        self.mutations(self.contract('E1M1CellObjectAdvance','execution',ADVANCE),[
            ('(ids : world.links[Collision.pathCellIndex x y w]?=some (nodes.map E1M1ThingList.Node.id).toArray)','(ids : True)'),
            ('(scene : ∀ node∈nodes, world.things[node.id]?=some node.target)','(scene : True)'),
            ('(dimension : world.grid.width=w)','(dimension : True)')])

if __name__=='__main__':unittest.main()

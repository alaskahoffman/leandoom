"""A complete cell must retain actual stack words, history and shared capacity."""
import re
import unittest
from pathlib import Path
import test_e1m1_cell_object_advance as prior
import verify_e1m1_cell_advance as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1CellObjectAdvance','import Doom.Proofs.E1M1CellAdvance')
HEADER+='open E1M1NextCallbackReady (Ready)\n'
HEADER+='attribute [local irreducible] E1M1CellLineBoundary.view E1M1CellAdvance.result E1M1CellScanAdvance.result\n'
BOUNDARY='s sp cursor lines objects trace c data stack list items ids ready layout f r tracked'
SCAN='s sp cursor base lines epoch words w h objects trace cell data nodes r seen pc stack list items ids target returnWord maps mapLayout payload payloadSafe contracts layout x y mapX mapY inMap links selection selectionSafe tracked capacity represented size stamps returns epochSafe stampSafe locals world dimension sceneIds scene'
GATE='s sp base lines epoch words w h objects trace cell data nodes r seen pc stack valid maps mapLayout payload payloadSafe contracts layout x y mapX mapY selected inMap links selection selectionSafe tracked cursorSafe recordsSafe capacity represented size stamps returns epochSafe stampSafe locals world dimension sceneIds scene'

class CellAdvanceTests(unittest.TestCase):
    lean=prior.CellObjectAdvanceTests.lean
    succeeds=prior.CellObjectAdvanceTests.succeeds
    rejects=prior.CellObjectAdvanceTests.rejects
    mutations=prior.CellObjectAdvanceTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        context=''
        if section:
            earlier=source[source.index('section Scan'):start]
            context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
            context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('CellLineBoundary.lookup_view','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_lookup_grid_view_uses_actual_saved_counter_and_stack(self):
        self.mutations(self.contract('E1M1CellLineBoundary','lookup_view','s sp stack'),[
            ('(stack : s.regs 4=sp-(112#32))','(stack : True)'),
            ('(view (E1M1PathMapCaller.scan s).core sp)','(view (E1M1PathMapCaller.scan s).core (sp+(4#32)))')])

    def test_line_numeric_boundary_requires_returns_and_local_protection(self):
        self.mutations(self.contract('E1M1CellLineBoundary','observe',BOUNDARY+' returns locals',True),[
            ('(returns : E1M1ScanReturn.ReturnSafe sp lines)','(returns : True)'),
            ('(locals : E1M1GridLocals.Safe sp lines)','(locals : True)'),
            ('E1M1PathAdvance.observe (view s sp)','E1M1PathAdvance.observe s')])

    def test_scan_entry_requires_real_callback_and_return_word(self):
        self.mutations(self.contract('E1M1CellScanAdvance','execution',SCAN),[
            ('(target : load32 s.core.memory (s.core.regs 4)=(0x2c5f0#32))','(target : True)'),
            ('(returnWord : load32 s.core.memory (sp-(116#32))=(0x2ca94#32))','(returnWord : True)'),
            ('(items : E1M1PathMapLookup.ScanWords s.core lines cell)','(items : True)')])

    def test_shared_capacity_counts_both_lists_without_refilling(self):
        self.mutations(self.contract('E1M1CellScanAdvance','execution',SCAN),[
            ('(capacity : r.collected.size+cell.ids.length+nodes.length≤128)',
             '(capacity : r.collected.size+nodes.length≤128)'),
            ('after.collected (128-(r.collected.size+cell.ids.length+nodes.length))',
             'after.collected (129-(r.collected.size+cell.ids.length+nodes.length))')])

    def test_lookup_must_select_the_current_cell_and_preserve_live_records(self):
        self.mutations(self.contract('E1M1CellAdvance','execution',GATE),[
            ('(selected : words[4+Collision.pathCellIndex x y w]?=some cell.offset)','(selected : True)'),
            ('(valid : cell.Valid words)','(valid : True)'),
            ('(cursorSafe : E1M1PathMapCaller.Safe s.core (0x2c028#32))','(cursorSafe : True)'),
            ('(recordsSafe : ∀ i<r.collected.size, ∀ off∈[(0#32),4,8],\n      E1M1PathMapCaller.Safe s.core (OriginalLineCollection.slot 0x2ba20 i off))','(recordsSafe : True)')])

    def test_gate_retains_original_step_control_and_instruction_bound(self):
        self.mutations(self.contract('E1M1CellAdvance','execution',GATE),[
            ('E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core)',
             'E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core'),
            ('out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core)','out.pc=0x2ca7f'),
            ('n≤89+281*cell.ids.length+230*nodes.length','n≤88+281*cell.ids.length+230*nodes.length')])

    def test_mutable_history_is_updated_and_must_survive_the_object_tail(self):
        self.mutations(self.contract('E1M1CellAdvance','execution',GATE),[
            ('(markPrefix (candidates trace lines cell.ids data) cell.ids.length 0 seen)','seen'),
            ('(stampSafe : ∀ j<475, TailSafe sp (stamp lines j))','(stampSafe : True)'),
            ('(represented : Represents s.core.memory lines epoch seen)','(represented : True)')])

    def test_scene_and_selection_are_transported_from_gate_not_assumed_after_scan(self):
        self.mutations(self.contract('E1M1CellAdvance','execution',GATE),[
            ('(payloadSafe : E1M1CellSceneInvariant.Protected sp lines cell data nodes)','(payloadSafe : True)'),
            ('(selection : E1M1CellObjectSelection.Image s.core.memory links x y w nodes)','(selection : True)'),
            ('(sceneIds : world.links[Collision.pathCellIndex x y w]?=some (nodes.map E1M1ThingList.Node.id).toArray)','(sceneIds : True)')])

if __name__=='__main__':unittest.main()

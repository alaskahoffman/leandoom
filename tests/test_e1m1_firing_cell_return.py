"""Coordinate restoration, finite-list induction and real caller TEST/JZ join."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_cell_return as proof
ROOT=Path(__file__).resolve().parents[1]
ARGS=previous.ARGS
FULL=ARGS+previous.HEAD+previous.DATA
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringCellReturn')
HEADER+='open OriginalLineCoordinates (register)\nopen E1M1ThingVisit (entry result)\nopen E1M1ThingList (Layout Image head run)\n'

class FiringCellReturnTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args,section=False):
        source=previous.FiringThingsTests.contract(self,module,name,args,section)
        return source.replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),28)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('traversal_coordinate','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_save_restore_uses_correct_stack_slots_and_registers(self):
        self.mutations(self.contract('E1M1ThingPreservation','slot_address','sp x'),[
            ('sp-(52#32)','sp-(48#32)')])
        self.mutations(self.contract('E1M1ThingPreservation','entry_saved','s x'),[
            ('=s.core.regs (register x)','=s.core.regs (register (!x))')])
        self.mutations(self.contract('E1M1ThingPreservation','finish_coordinate','s x'),[
            ('s.core.regs 4+popOffset x','s.core.regs 4+popOffset x+(4#32)')])

    def test_visit_protection_requires_existing_layout_and_capacity(self):
        self.mutations(self.contract('E1M1ThingPreservation','visit_coordinate','s trace target h resolve r tracked capacity x'),[
            ('(h : E1M1ThingVisit.Inputs s trace target)','(h : True)'),
            ('(capacity : r.collected.size<128)','(capacity : r.collected.size≤128)'),
            ('(tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)','(tracked : True)')])

    def test_full_list_restoration_needs_initial_image_and_room(self):
        self.mutations(self.contract('E1M1ThingPreservation','traversal_coordinate',
            's trace resolve nodes ret layout image cursor pc r tracked capacity x'),[
            ('(image : Image s.core.memory (s.core.regs 4) trace nodes ret)','(image : True)'),
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : r.collected.size≤128)'),
            ('(layout : Layout (s.core.regs 4) trace resolve nodes)','(layout : True)')])

    def test_success_branch_is_executed_and_failure_cannot_pass(self):
        self.mutations(self.contract('E1M1FiringCellReturn','success_test','s pc success'),[
            ('(success : s.core.regs 0=(1#32))','(success : s.core.regs 0=(0#32))'),
            ('(pc : s.pc=0x2cab1)','(pc : s.pc=0x2cab3)'),
            ('program [] 2 s','program [] 1 s'),
            ('.pc=0x2cab5','.pc=0x2cb0b')])

    def test_firing_join_retains_coordinates_collection_and_bound(self):
        self.mutations(self.contract('E1M1FiringCellReturn','firing_coordinate',FULL+' room x',True),[
            ('(room : c.ids.length+nodes.length≤128)','(room : True)')])
        self.mutations(self.contract('E1M1FiringCellReturn','execution',FULL+' room world dimension ids scene f',True),[
            ('steps≤408+','steps≤407+'),
            ('out.pc=0x2cab5','out.pc=0x2cab1'),
            ('out.core.regs 6=(path thing angle ox oy).startBlockX.toBitVec','out.core.regs 6=(path thing angle ox oy).startBlockY.toBitVec'),
            ('(dimension : world.grid.width=w)','(dimension : True)')])

    def test_nonzero_coordinates_wraparound_stack_and_both_branches(self):
        source=(ROOT/'tests/reference/original-firing-cell-return.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('out.core.regs 1=0x89abcdef','out.core.regs 1=0xfedcba98'))

if __name__=='__main__':unittest.main()

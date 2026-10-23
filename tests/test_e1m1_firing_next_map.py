"""Persistent map values and remaining capacity must survive the actual cell path."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_numeric as prior
import verify_e1m1_firing_next_map as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextNumeric','import Doom.Proofs.E1M1FiringNextMap')
HEADER+='attribute [local irreducible] E1M1PathMapCaller.scan E1M1FiringCellReturn.result\n'
NEXT=prior.NEXT
LOOKUP=prior.LOOKUP
MAP='s sp base lines words w h stack image layout'
GATE='s sp base lines words w h pc stack image layout x y mapX mapY c inMap valid selected resolve hits reserve tracked cursorSafe recordsSafe epoch seen represented epochSafe stampSafe'

class FiringNextMapTests(unittest.TestCase):
    lean=prior.FiringNextNumericTests.lean
    succeeds=prior.FiringNextNumericTests.succeeds
    rejects=prior.FiringNextNumericTests.rejects
    mutations=prior.FiringNextNumericTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        context=''
        if section:
            earlier=source[source.index('section Firing'):start]
            context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
            context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('CellMapInvariant.transport','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_frame_composition_requires_both_actual_segments(self):
        self.mutations(self.contract('E1M1CellMapInvariant','frame_trans','sp lines a b c ab bc'),[
            ('(ab : Frame sp lines a b)','(ab : True)'),
            ('(bc : Frame sp lines b c)','(bc : True)')])

    def test_image_transport_requires_read_frame_and_separation(self):
        self.mutations(self.contract('E1M1CellMapInvariant','transport','m n sp base lines words w h image layout frame'),[
            ('(layout : Layout sp base lines words)','(layout : True)'),
            ('(frame : Frame sp lines m n)','(frame : True)'),
            ('Image n sp base lines words w h :=','Image n sp base lines words (w+1) h :=')])

    def test_enabled_bits_need_the_initialized_image_and_caller_stack(self):
        self.mutations(self.contract('E1M1CellMapInvariant','enabled','s sp base lines words w h stack image line'),[
            ('(stack : s.regs 4=sp-(112#32))','(stack : True)'),
            ('OriginalPathCell.enabled line s=true','OriginalPathCell.enabled line s=false')])

    def test_lookup_inputs_need_protected_globals_and_map_words(self):
        self.mutations(self.contract('E1M1CellMapInvariant','inputs',MAP),[
            ('(layout : Layout sp base lines words)','(layout : True)'),
            ('(image : Image s.memory sp base lines words w h)','(image : True)')])

    def test_lookup_preserves_existing_reserve_and_real_control(self):
        self.mutations(self.contract('E1M1CellMapInvariant','inside',GATE),[
            ('OriginalLineCollection.Tracks out.core 0x2ba20 resolve hits reserve',
             'OriginalLineCollection.Tracks out.core 0x2ba20 resolve hits (reserve+1)'),
            ('out.pc=0x2c57f','out.pc=0x2ca7f'),
            ('out.core.regs 4=sp-(124#32)','out.core.regs 4=sp-(112#32)'),
            ('n≤30','n≤29')])

    def test_lookup_needs_mutable_record_and_stamp_protection(self):
        self.mutations(self.contract('E1M1CellMapInvariant','inside',GATE),[
            ('(cursorSafe : E1M1PathMapCaller.Safe s.core (0x2c028#32))','(cursorSafe : True)'),
            ('(recordsSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],\n      E1M1PathMapCaller.Safe s.core (OriginalLineCollection.slot 0x2ba20 i off))','(recordsSafe : True)'),
            ('(epochSafe : E1M1PathMapCaller.Safe s.core (0x13580#32))','(epochSafe : True)'),
            ('(stampSafe : ∀ j<seen.size, E1M1PathMapCaller.Safe s.core (OriginalLineVisits.stamp lines j))','(stampSafe : True)')])

    def test_prepared_frame_comes_from_the_actual_prior_cell(self):
        self.mutations(self.contract('E1M1NextLookupFrame','prepared',LOOKUP,True),[
            ('(budget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128)',
             '(budget : c.ids.length+nodes.length≤128)'),
            ('after.collected.size≤c.ids.length+nodes.length ∧','after.collected.size≤c.ids.length ∧')])

    def test_joined_image_and_capacity_have_the_proved_values(self):
        self.mutations(self.contract('E1M1FiringNextMap','execution',NEXT,True),[
            ('final.collected (128-(c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length))',
             'final.collected (129-(c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length))'),
            ('E1M1CellMapInvariant.Image out.core.memory (s.regs 4) base lines words w h',
             'E1M1CellMapInvariant.Image out.core.memory (s.regs 4) base lines words (w+1) h'),
            ('(nextScene : ∀ node∈nextNodes, world.things[node.id]?=some node.target)','(nextScene : True)')])

if __name__=='__main__':unittest.main()

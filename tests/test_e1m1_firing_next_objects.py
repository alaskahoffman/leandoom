"""The second object list needs derived memory, real capacity and exact scene order."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_lookup as prior
import verify_e1m1_firing_next_objects as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextLookup','import Doom.Proofs.E1M1FiringNextObjects')
HEADER+='open E1M1ThingList (head collect Image Layout)\n'
SCAN=prior.SCAN+' returns f r tracked'
IMAGE=prior.prior.NEXT+' nextNodes headValue nextSetup nextSafe nextObjects nextObjectSafe nextLinkSafe totalBudget'
NEXT=prior.prior.NEXT.removesuffix(' budget')+' nextNodes headValue nextSetup nextSafe nextObjects nextObjectSafe nextLinkSafe totalBudget nextIds nextScene'
TRAVERSE='s sp lines epoch objects trace nodes r seen nonzero empty nonempty ready tracked capacity represented epochSafe stampSafe'

class FiringNextObjectsTests(unittest.TestCase):
    lean=prior.FiringNextLookupTests.lean
    succeeds=prior.FiringNextLookupTests.succeeds
    rejects=prior.FiringNextLookupTests.rejects
    mutations=prior.FiringNextLookupTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        context=''
        if section:
            label='Scan' if module=='E1M1NextObjectMemory' else 'Firing'
            earlier=source[source.index('section '+label):start]
            context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
            context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('FiringNextObjects.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_scan_size_keeps_the_incoming_mixed_collection(self):
        self.mutations(self.contract('E1M1NextObjectMemory','scan_size','s lines trace c data f r'),[
            ('r.collected.size+c.ids.length','c.ids.length'),
            ('r.collected.size+c.ids.length','r.collected.size')])

    def test_read_transport_requires_real_scan_and_store_protection(self):
        self.mutations(self.contract('E1M1NextObjectMemory','read_word',SCAN+' a safe',True),[
            ('(safe : E1M1FiringMapState.Safe sp lines a)','(safe : True)'),
            ('(returns : E1M1ScanReturn.ReturnSafe sp lines)','(returns : True)'),
            ('r.collected c.ids.length)','r.collected 0)')])

    def test_caller_word_comes_from_call_at_the_correct_stack_slot(self):
        self.mutations(self.contract('E1M1NextObjectMemory','caller_word',SCAN,True),[
            ('memory (sp-(116#32))=(0x2cab1#32)','memory (sp-(120#32))=(0x2cab1#32)'),
            ('=(0x2cab1#32) :=','=(0x2ca94#32) :='),
            ('(returns : E1M1ScanReturn.ReturnSafe sp lines)','(returns : True)')])

    def test_image_needs_initial_node_values_links_and_lifetime_separation(self):
        self.mutations(self.contract('E1M1FiringNextObjectImage','execution',IMAGE,True),[
            ('(nextObjects : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nextNodes)','(nextObjects : True)'),
            ('(nextObjectSafe : ∀ node∈nextNodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer,\n      E1M1FiringMapState.Safe (s.regs 4) lines a)','(nextObjectSafe : True)'),
            ('(nextLinkSafe : ∀ node∈nextNodes,\n      E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32)))','(nextLinkSafe : True)'),
            ('(totalBudget : c.ids.length+nodes.length+nextCell.ids.tail.length+nextNodes.length≤128)',
             '(totalBudget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128)')])

    def test_reused_traversal_requires_capacity_and_actual_list_image(self):
        self.mutations(self.contract('E1M1NextObjectTraversal','execution',TRAVERSE),[
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : r.collected.size≤128)'),
            ('(ready : head nodes≠0 → Image s.core.memory (s.core.regs 4) trace nodes (0x2cab1#32) ∧\n      Layout (s.core.regs 4) trace (E1M1ThingFinish.resolve lines objects) nodes)','(ready : True)'),
            ('n≤230*nodes.length+3','n≤230*nodes.length+2')])

    def test_object_callbacks_preserve_the_actual_visited_history(self):
        self.mutations(self.contract('E1M1NextObjectTraversal','execution',TRAVERSE),[
            ('(epochSafe : E1M1ThingVisit.ReadSafe (sp-(120#32)) (0x13580#32))','(epochSafe : True)'),
            ('(stampSafe : ∀ j<seen.size, E1M1ThingVisit.ReadSafe (sp-(120#32)) (stamp lines j))','(stampSafe : True)'),
            ('Represents out.core.memory lines epoch seen :=','Represents out.core.memory lines (epoch+1) seen :=')])

    def test_continuous_execution_uses_exact_next_scene_cell_and_nodes(self):
        self.mutations(self.contract('E1M1FiringNextObjects','execution',NEXT,True),[
            ('(nextIds : world.links[Collision.pathCellIndex x y w]?=some (nextNodes.map E1M1ThingList.Node.id).toArray)','(nextIds : True)'),
            ('(nextScene : ∀ node∈nextNodes, world.things[node.id]?=some node.target)','(nextScene : True)'),
            ('(headValue : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=(E1M1ThingList.head nextNodes))','(headValue : True)')])

    def test_joined_bound_and_caller_return_cover_both_object_lists(self):
        self.mutations(self.contract('E1M1FiringNextObjects','execution',NEXT,True),[
            ('steps≤505+281*(c.ids.length+nextCell.ids.tail.length)+230*(nodes.length+nextNodes.length)',
             'steps≤504+281*(c.ids.length+nextCell.ids.tail.length)+230*(nodes.length+nextNodes.length)'),
            ('out.core.regs 4=s.regs 4-(112#32)','out.core.regs 4=s.regs 4-(120#32)'),
            ('out.pc=0x2cab1','out.pc=0x2c5d2')])

if __name__=='__main__':unittest.main()

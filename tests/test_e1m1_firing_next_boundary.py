"""The reusable cell boundary must retain numeric state, hits, history and safe reads."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_objects as prior
import verify_e1m1_firing_next_boundary as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextObjects','import Doom.Proofs.E1M1FiringNextBoundary')
HEADER+='open E1M1NextObjectTraversal (result)\nopen E1M1PathAdvance (Cell observe step nextPc)\n'
OBJECT='s sp lines objects trace nodes r nonzero empty nonempty ready tracked capacity'
ADVANCE='s sp lines epoch objects g hits seen ready locals epochSafe stampSafe'
NEXT=prior.NEXT

class FiringNextBoundaryTests(unittest.TestCase):
    lean=prior.FiringNextObjectsTests.lean
    succeeds=prior.FiringNextObjectsTests.succeeds
    rejects=prior.FiringNextObjectsTests.rejects
    mutations=prior.FiringNextObjectsTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        context=''
        if section:
            label='Objects' if module=='E1M1ObjectBoundary' else 'Firing'
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
                    out+'extra',out.replace('FiringNextBoundary.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_object_preservation_requires_actual_capacity_and_representation(self):
        self.mutations(self.contract('E1M1ObjectBoundary','preserved',OBJECT,True),[
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : r.collected.size≤128)'),
            ('(ready : head nodes≠0 → Image s.core.memory (s.core.regs 4) trace nodes (0x2cab1#32) ∧\n      Layout (s.core.regs 4) trace (E1M1ThingFinish.resolve lines objects) nodes)','(ready : True)'),
            ('out.core.regs 4=sp-(112#32)','out.core.regs 4=sp-(120#32)'),
            ('∀ a, E1M1ThingVisit.ReadSafe (sp-(120#32)) a →','∀ a, True →')])

    def test_numeric_observation_uses_caller_stack_and_protected_locals(self):
        self.mutations(self.contract('E1M1ObjectBoundary','observe',OBJECT+' locals',True),[
            ('(locals : E1M1GridLocals.Safe sp lines)','(locals : True)'),
            ('(callerView s sp) :=','(callerView s (sp+(4#32))) :=')])

    def test_advance_frame_requires_the_actual_possible_store_address(self):
        self.mutations(self.contract('E1M1CellBoundaryAdvance','frame','s sp stack a safe'),[
            ('(safe : Apart a (sp-(112#32)+(44#32)))','(safe : True)'),
            ('(safe : Apart a (sp-(112#32)+(44#32)))','(safe : Apart a (sp-(112#32)+(40#32)))'),
            ('(stack : s.core.regs 4=sp-(112#32))','(stack : True)')])

    def test_cell_transition_needs_returned_state_and_heap_separation(self):
        self.mutations(self.contract('E1M1CellBoundaryAdvance','execution',ADVANCE),[
            ('(ready : Returned s sp lines epoch objects g hits seen)','(ready : True)'),
            ('(locals : E1M1GridLocals.Safe sp lines)','(locals : True)'),
            ('(epochSafe : Apart (0x13580#32) (sp-(112#32)+(44#32)))','(epochSafe : True)'),
            ('(stampSafe : ∀ j<seen.size, Apart (stamp lines j) (sp-(112#32)+(44#32)))','(stampSafe : True)')])

    def test_transition_has_original_numeric_step_and_pc(self):
        self.mutations(self.contract('E1M1CellBoundaryAdvance','execution',ADVANCE),[
            ('observe out.core=step g','observe out.core=g'),
            ('out.pc=nextPc g','out.pc=0x2ca7f'),
            ('n≤21','n≤20')])

    def test_joined_boundary_retains_production_hits_and_original_control(self):
        self.mutations(self.contract('E1M1FiringNextBoundary','execution',NEXT,True),[
            ('steps≤526+281*(c.ids.length+nextCell.ids.tail.length)+230*(nodes.length+nextNodes.length)',
             'steps≤525+281*(c.ids.length+nextCell.ids.tail.length)+230*(nodes.length+nextNodes.length)'),
            ('E1M1PathAdvance.observe out.core=E1M1PathAdvance.step grid','E1M1PathAdvance.observe out.core=grid'),
            ('out.pc=E1M1PathAdvance.nextPc grid','out.pc=0x2ca7f'),
            ('(nextScene : ∀ node∈nextNodes, world.things[node.id]?=some node.target)','(nextScene : True)')])

    def test_joined_read_frame_needs_both_object_and_advance_protection(self):
        self.mutations(self.contract('E1M1FiringNextBoundary','execution',NEXT,True),[
            ('(∀ a, E1M1ThingVisit.ReadSafe (s.regs 4-(120#32)) a →','(∀ a, True →'),
            ('Apart a (s.regs 4-(112#32)+(44#32)) → load32 out.core.memory a=load32 entry.core.memory a)',
             'True → load32 out.core.memory a=load32 entry.core.memory a)')])

if __name__=='__main__':unittest.main()

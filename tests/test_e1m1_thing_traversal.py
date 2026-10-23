"""Finite original object-list induction, frame preservation, and caller return."""
import copy
import json
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_thing_traversal as proof
import verify_original_inline_thrust as extraction
HEADER='''import Doom.Proofs.E1M1ThingTraversal
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ThingVisit (ReadSafe StackSafe Geometry Inputs)
open E1M1ThingList (Layout Image head collect run)
open OriginalThingSecondSide (firstSide lastSide)
attribute [local irreducible] load32 OriginalDivlineSide.result OriginalThingSecondSide.result OriginalThingFraction.result
attribute [local irreducible] Collision.thingIntercept Collision.interceptVector Collision.Divline.pointSide
'''
LIST_ARGS='s trace resolve nodes ret layout image cursor pc r tracked capacity'

class ThingTraversalTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

    def contract(self,module,name,args):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[source.index('theorem '+name+' '):],maxsplit=1)[0]
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),28)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('execution_cell','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_pinned_iterator_return_bytes_fail_closed(self):
        spec=json.loads((ROOT/'tests/reference/original-thing-entry.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text())
        share=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=extraction.original.extract(ROOT/share['local_directory']/'doom19s.zip',share,profile)
        extraction.extract(binary,profile,spec)
        for kind in ['return_value','stack_delta','file']:
            bad=copy.deepcopy(spec);unit=bad['units']['thingReturn']
            if kind=='return_value':unit['hex']=unit['hex'].replace('b801','b800')
            elif kind=='stack_delta':unit['hex']=unit['hex'].replace('83c404','83c408')
            else:unit['file_offset']='0x1'
            with self.subTest(kind=kind),self.assertRaises(ValueError):extraction.extract(binary,profile,bad)

    def test_complete_visit_requires_live_inputs_pointer_and_capacity(self):
        self.mutations(self.contract('E1M1ThingVisit','execution','s trace target h pc resolve id r pointer tracked capacity'),[
            ('(h : Inputs s trace target)','(h : True)'),
            ('(pointer : ∀ frac, resolve ⟨frac,false,id⟩=s.core.regs 2)','(pointer : True)'),
            ('(capacity : r.collected.size<128)','(capacity : r.collected.size≤128)'),
            ('∃ n≤230','∃ n≤229')])

    def test_frame_requires_separation_through_every_write(self):
        self.mutations(self.contract('E1M1ThingVisit','frame','s trace target h resolve r tracked capacity a safe'),[
            ('(safe : ReadSafe (s.core.regs 4) a)','(safe : True)')])
        self.mutations(self.contract('E1M1ThingList','linked_transport','before after nodes h keep'),[
            ('(h : Linked before nodes)','(h : True)'),
            ('load32 after (node.pointer+(44#32))=load32 before (node.pointer+(44#32))','load32 after (node.pointer+(40#32))=load32 before (node.pointer+(40#32))')])

    def test_list_induction_requires_initial_image_layout_and_whole_list_capacity(self):
        self.mutations(self.contract('E1M1ThingList','execution',LIST_ARGS),[
            ('(layout : Layout (s.core.regs 4) trace resolve nodes)','(layout : True)'),
            ('(image : Image s.core.memory (s.core.regs 4) trace nodes ret)','(image : True)'),
            ('(cursor : s.core.regs 2=head nodes)','(cursor : True)'),
            ('r.collected.size+nodes.length≤128','r.collected.size+nodes.length≤129')])

    def test_return_uses_saved_caller_and_exact_stack_adjustment(self):
        self.mutations(self.contract('E1M1ThingTraversal','return_observe','s'),[
            ('(s.regs 4+(4#32))','(s.regs 4+(8#32))'),
            ('s.regs 4+(8#32)','s.regs 4+(4#32)'),
            ('regs 0=(1#32)','regs 0=(0#32)')])
        self.mutations(self.contract('E1M1ThingTraversal','execution',LIST_ARGS),[
            ('230*nodes.length+3','230*nodes.length+2'),
            ('out.pc=ret.toNat','out.pc=0x2cab1')])

    def test_production_scene_loop_needs_actual_id_lookup(self):
        self.mutations(self.contract('E1M1ThingTraversal','objectCell_collect','trace things nodes r lookup'),[
            ('(lookup : ∀ node∈nodes, things[node.id]?=some node.target)','(lookup : True)')])
        self.mutations(self.contract('E1M1ThingTraversal','execution_cell',LIST_ARGS+' things lookup'),[
            ('(lookup : ∀ node∈nodes, things[node.id]?=some node.target)','(lookup : True)'),
            ('out.core.regs 4=s.core.regs 4+(8#32)','out.core.regs 4=s.core.regs 4+(4#32)')])

    def test_growth_bound_preserves_capacity(self):
        self.mutations(self.contract('E1M1ThingList','collect_size','trace target id r after ok'),[
            ('after.collected.size≤r.collected.size+1','after.collected.size≤r.collected.size'),
            ('(ok : E1M1ThingFinish.collect trace target id r=.ok after)','(ok : True)')])

    def test_ordered_ties_rejection_empty_wrap_and_overflow_fixture(self):
        source=(ROOT/'tests/reference/original-thing-traversal.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('load32 out.core.memory 0x2ba40=0x700c01','load32 out.core.memory 0x2ba40=0x700801'))

if __name__=='__main__':unittest.main()

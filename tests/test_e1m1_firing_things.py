"""Initial-state object-list transport and continuous firing-to-cell-return proof."""
import re
import sys
import unittest
from pathlib import Path
import test_e1m1_weapon_runtime as runtime
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_e1m1_firing_things as proof
HEADER='''import Doom.Proofs.E1M1FiringThings
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (boundary before)
attribute [local irreducible] Collision.SolidThing.attackEndpoint load32
attribute [local irreducible] OriginalDivlineSide.result OriginalThingSecondSide.result OriginalThingFraction.result
'''
ARGS='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'
HEAD=' returns flag links nodes lookupSafe global selected'
DATA=' objects d'

class FiringThingsTests(unittest.TestCase):
    lean=runtime.WeaponRuntimeTests.lean
    succeeds=runtime.WeaponRuntimeTests.succeeds

    def rejects(self,source):
        out=self.lean(source)
        self.assertNotEqual(out.returncode,0,out.stdout)
        self.assertIn('error:',out.stdout)
        for bad in ['maximum','timeout','object file','unknown module prefix','unknown identifier','unknown constant']:
            self.assertNotIn(bad,out.stdout.lower())

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

    def mutations(self,source,changes):
        self.succeeds(source)
        for old,new in changes:
            self.assertIn(old,source)
            with self.subTest(change=old):self.rejects(source.replace(old,new))

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),28)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),out+'extra',out.replace('execution_scene','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_candidate_bound_supplies_whole_cell_capacity(self):
        self.mutations(self.contract('E1M1ScanCapacity','step_size','c s r'),[
            ('r.collected.size+1','r.collected.size')])
        self.mutations(self.contract('E1M1ThingListInputs','capacity',ARGS+' nodes room',True),[
            ('c.ids.length+nodes.length≤128','c.ids.length+nodes.length≤129'),
            ('c.ids.length+nodes.length≤128','nodes.length≤128')])

    def test_initial_object_reads_require_full_prefix_separation(self):
        self.mutations(self.contract('E1M1ThingListInputs','entry_read',ARGS+' returns a safe',True),[
            ('(safe : E1M1ThingEntry.ReadSafe gun s lines a)','(safe : True)')])
        self.mutations(self.contract('E1M1ThingListInputs','trace_read',ARGS+' returns a scan call entry',True),[
            ('(scan : E1M1ThingGeometry.ScanSafe (s.regs 4) lines a)','(scan : True)'),
            ('(entry : Apart a (s.regs 4-(120#32)))','(entry : True)')])

    def test_geometry_and_link_image_are_derived_from_initial_data(self):
        self.mutations(self.contract('E1M1ThingListInputs','geometry',ARGS+' returns objects nodes d node member',True),[
            ('(d : Data gun s lines (path thing angle ox oy).trace objects nodes)','(d : True)'),
            ('(member : node∈nodes)','(member : True)')])
        self.mutations(self.contract('E1M1ThingListInputs','linked',ARGS+' returns objects nodes d',True),[
            ('(d : Data gun s lines (path thing angle ox oy).trace objects nodes)','(d : True)')])

    def test_saved_words_come_from_real_call_and_prologue(self):
        self.mutations(self.contract('E1M1FiringThings','saved_words',ARGS+HEAD+' present',True),[
            ('(present : E1M1ThingList.head nodes≠(0#32))','(present : True)'),
            ('=(0x2c720#32)','=(0x2c5f0#32)'),
            ('=(0x2cab1#32)','=(0x2c5d7#32)')])

    def test_list_contract_requires_raw_data_not_reached_outcomes(self):
        self.mutations(self.contract('E1M1FiringThings','image',ARGS+HEAD+DATA+' present',True),[
            ('(d : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nodes)','(d : True)')])
        self.mutations(self.contract('E1M1FiringThings','layout',ARGS+HEAD+DATA+' present',True),[
            ('(present : E1M1ThingList.head nodes≠(0#32))','(present : True)')])
        fields=(ROOT/'Doom/Proofs/E1M1ThingListInputs.lean').read_text().split('section Firing')[0]
        for reached in ['boundary','Outcome','Prefix','E1M1ThingList.Image']:
            self.assertNotIn(reached,fields)

    def test_full_firing_join_bound_stack_and_capacity(self):
        self.mutations(self.contract('E1M1FiringThings','execution',ARGS+HEAD+DATA+' room things scene f',True),[
            ('steps≤406+281*c.ids.length+230*nodes.length','steps≤405+281*c.ids.length+230*nodes.length'),
            ('out.core.regs 4=s.regs 4-(112#32)','out.core.regs 4=s.regs 4-(116#32)'),
            ('out.pc=0x2cab1','out.pc=0x2c5d2'),
            ('(room : c.ids.length+nodes.length≤128)','(room : True)')])

    def test_selected_scene_cell_cannot_be_substituted(self):
        self.mutations(self.contract('E1M1FiringThings','scene_cell','trace world x y width nodes r dimension ids'),[
            ('(dimension : world.grid.width=width)','(dimension : True)'),
            ('Collision.pathCellIndex x y width','Collision.pathCellIndex y x width')])
        self.mutations(self.contract('E1M1FiringThings','execution_scene',ARGS+HEAD+DATA+' room world dimension ids scene f',True),[
            ('(dimension : world.grid.width=w)','(dimension : True)'),
            ('(scene : ∀ node∈nodes, world.things[node.id]?=some node.target)','(scene : True)')])

    def test_scene_order_empty_missing_invalid_and_capacity_fixture(self):
        source=(ROOT/'tests/reference/original-firing-things.lean').read_text()
        self.assertNotIn('sorryAx',self.succeeds(source))
        self.rejects(source.replace('false,2⟩,⟨⟨65536⟩,false,0','false,0⟩,⟨⟨65536⟩,false,2'))

if __name__=='__main__':unittest.main()

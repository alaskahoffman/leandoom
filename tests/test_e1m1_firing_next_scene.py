"""Reusable callback readiness requires real persistent data and fresh stack words."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_map as prior
import verify_e1m1_firing_next_scene as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextMap','import Doom.Proofs.E1M1FiringNextScene')
NEXT=prior.NEXT
COMMON='gun s weapon actor thing angle ox oy xout yout base lines words c w h data input'
INITIAL=COMMON+' returns flag links nodes lookupSafe global selected objects d room world dimension ids scene cell lineData lineInput objectNodes objectInput objectSafe linkSafe traceSafe activeSafe'
READY='s sp lines trace cell data objects nodes image contracts'

class FiringNextSceneTests(unittest.TestCase):
    lean=prior.FiringNextMapTests.lean
    succeeds=prior.FiringNextMapTests.succeeds
    rejects=prior.FiringNextMapTests.rejects
    mutations=prior.FiringNextMapTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=source.index('theorem '+name+' ')
        context=''
        if section:
            earlier=source[source.index('section Firing'):start]
            context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
            context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        header=HEADER
        if module=='E1M1FiringSceneData':
            header+='open E1M1CellSceneInvariant (Image Protected Contracts)\n'
        return header+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('CellSceneInvariant.transport','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_transport_requires_actual_image_protection_and_frame(self):
        self.mutations(self.contract('E1M1CellSceneInvariant','transport','m n sp lines trace cell data nodes image safe frame'),[
            ('(image : Image m lines trace cell data nodes)','(image : True)'),
            ('(safe : Protected sp lines cell data nodes)','(safe : True)'),
            ('(frame : E1M1CellMapInvariant.Frame sp lines m n)','(frame : True)')])

    def test_line_templates_need_actual_target_pointers_and_storage(self):
        self.mutations(self.contract('E1M1CellSceneInvariant','lines_ready',READY+' stack target items ids'),[
            ('(target : load32 s.memory (s.regs 4)=(0x2c5f0#32))','(target : True)'),
            ('(contracts : Contracts sp lines trace cell data objects nodes)','(contracts : True)'),
            ('(items : E1M1PathMapLookup.ScanWords s lines cell)','(items : True)'),
            ('(ids : ∀ i : Fin cell.ids.length, cell.ids[i.val]<475)','(ids : True)')])

    def test_object_image_needs_fresh_callback_and_caller_words(self):
        self.mutations(self.contract('E1M1CellSceneInvariant','objects_ready',READY+' stack callback caller'),[
            ('(callback : load32 s.memory (s.regs 4)=(0x2c720#32))','(callback : True)'),
            ('(caller : load32 s.memory (sp-(116#32))=(0x2cab1#32))','(caller : True)'),
            ('(stack : s.regs 4=sp-(120#32))','(stack : s.regs 4=sp-(112#32))'),
            ('trace nodes (0x2cab1#32) ∧','trace nodes (0x2ca94#32) ∧')])

    def test_lookup_derives_line_callback_word_from_real_prologue(self):
        args='s sp lines trace cell data objects nodes image safe contracts stack scanStack items ids'
        self.mutations(self.contract('E1M1CellSceneInvariant','lookup_ready',args),[
            ('(stack : s.regs 4=sp-(112#32))','(stack : True)'),
            ('(scanStack : (E1M1PathMapCaller.scan s).core.regs 4=sp-(124#32))','(scanStack : True)'),
            ('(safe : Protected sp lines cell data nodes)','(safe : True)')])

    def test_initial_future_data_requires_initial_encodings(self):
        self.mutations(self.contract('E1M1FiringSceneData','prepared',INITIAL,True),[
            ('(lineInput : E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace cell lineData)',
             '(lineInput : True)'),
            ('(objectInput : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects objectNodes)',
             '(objectInput : True)')])

    def test_initial_future_data_requires_geometry_and_link_lifetime(self):
        self.mutations(self.contract('E1M1FiringSceneData','prepared',INITIAL,True),[
            ('(objectSafe : ∀ node∈objectNodes, ∀ a∈E1M1ThingGeometry.objectReads node.pointer,\n      E1M1FiringMapState.Safe (s.regs 4) lines a)','(objectSafe : True)'),
            ('(linkSafe : ∀ node∈objectNodes, E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32)))','(linkSafe : True)'),
            ('(activeSafe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32))','(activeSafe : True)')])

    def test_joined_future_data_is_conditional_on_real_initial_representation(self):
        self.mutations(self.contract('E1M1FiringNextScene','execution',NEXT,True),[
            ('E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace cell lineData →', 'True →'),
            ('E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects objectNodes →', 'True →'),
            ('(∀ node∈objectNodes, E1M1FiringMapState.Safe (s.regs 4) lines (node.pointer+(44#32))) →','True →'),
            ('steps≤526+','steps≤525+')])

if __name__=='__main__':unittest.main()

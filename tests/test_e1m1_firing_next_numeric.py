"""Second-cell numeric equality must come from initialization and actual execution."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_next_boundary as prior
import verify_e1m1_firing_next_numeric as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=prior.HEADER.replace('import Doom.Proofs.E1M1FiringNextBoundary','import Doom.Proofs.E1M1FiringNextNumeric')
# Keep wrong-step checks focused on the contract instead of expanding the engine.
HEADER+='attribute [local irreducible] E1M1PathAdvance.step\n'
SCAN=prior.prior.SCAN
NEXT=prior.NEXT
LOOKUP=NEXT.split(' nextNodes')[0]+' budget after production'

class FiringNextNumericTests(unittest.TestCase):
    lean=prior.FiringNextBoundaryTests.lean
    succeeds=prior.FiringNextBoundaryTests.succeeds
    rejects=prior.FiringNextBoundaryTests.rejects
    mutations=prior.FiringNextBoundaryTests.mutations

    def contract(self,module,name,args,section=False):
        source=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
        start=re.search(r'^theorem '+name+r'(?: | :)',source,re.M).start()
        context=''
        if section:
            label='Scan' if module=='E1M1NextScanGrid' else 'Firing'
            earlier=source[source.index('section '+label):start]
            context=''.join(re.findall(r'^variable .*?(?=^include)',earlier,re.M|re.S))
            context+='\n'.join(re.findall(r'^include .+$',earlier,re.M))+'\n'
        decl=re.split(r' :=(?: by)?(?:\n| rfl)',source[start:],maxsplit=1)[0]
        # The generic scan result has its own short name, not the object traversal's.
        header=HEADER.replace('open E1M1NextObjectTraversal (result)','open E1M1NextObjectMemory (result)')
        return header+'namespace Doom.Proofs.'+module+'\n'+context+decl.replace('theorem '+name,'example',1)+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29);self.assertEqual(len(data['cells']),828)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('NextLookupGrid.observe','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+)(?: | :)',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_lookup_retains_only_the_actual_grid_registers(self):
        self.mutations(self.contract('E1M1NextScanGrid','lookup_register','s reg member'),[
            ('([1,5,6,7] : List (Fin 8))','([0,1,5,6,7] : List (Fin 8))'),
            ('=s.core.regs reg :=','=s.core.regs reg+1 :=')])

    def test_caller_locals_use_the_returned_stack(self):
        self.mutations(self.contract('E1M1NextScanGrid','caller_local','s sp stack off member'),[
            ('(stack : s.regs 4=sp-(112#32))','(stack : True)'),
            ('(member : off∈E1M1GridLocals.offsets)','(member : True)')])

    def test_scan_reads_require_scan_and_call_separation(self):
        self.mutations(self.contract('E1M1NextScanGrid','read_word',SCAN+' a scanSafe callSafe entrySafe',True),[
            ('(scanSafe : E1M1ThingGeometry.ScanSafe sp lines a)','(scanSafe : True)'),
            ('(callSafe : Apart a (sp-(116#32)))','(callSafe : True)'),
            ('(entrySafe : Apart a (sp-(120#32)))','(entrySafe : True)')])

    def test_all_seven_locals_need_heap_protection(self):
        self.mutations(self.contract('E1M1NextScanGrid','local_word',SCAN+' locals off member',True),[
            ('(locals : E1M1GridLocals.Safe sp lines)','(locals : True)'),
            ('(member : off∈E1M1GridLocals.offsets)','(member : True)')])

    def test_counter_is_restored_from_the_actual_saved_slot(self):
        self.mutations(self.contract('E1M1NextScanGrid','registers',SCAN,True),[
            ('out.core.regs 7=load32 s.memory (sp-(120#32))','out.core.regs 7=s.regs 7'),
            ('out.core.regs 7=load32 s.memory (sp-(120#32))','out.core.regs 7=load32 s.memory (sp-(116#32))'),
            ('(returns : E1M1ScanReturn.ReturnSafe sp lines)','(returns : True)')])

    def test_lookup_is_the_initialized_first_step(self):
        self.mutations(self.contract('E1M1NextLookupGrid','observe',LOOKUP,True),[
            ('E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout) :=',
             'initial (path thing angle ox oy) xout yout :='),
            ('(budget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128)',
             '(budget : c.ids.length+nodes.length≤128)'),
            ('(locals : E1M1GridLocals.Safe (s.regs 4) lines)','(locals : True)')])

    def test_joined_result_is_two_steps_with_original_pc_and_records(self):
        self.mutations(self.contract('E1M1FiringNextNumeric','execution',NEXT,True),[
            ('E1M1PathAdvance.observe out.core=E1M1PathAdvance.step grid','E1M1PathAdvance.observe out.core=grid'),
            ('out.pc=E1M1PathAdvance.nextPc grid','out.pc=0x2ca7f'),
            ('steps≤526+','steps≤525+'),
            ('(nextScene : ∀ node∈nextNodes, world.things[node.id]?=some node.target)','(nextScene : True)')])

if __name__=='__main__':unittest.main()

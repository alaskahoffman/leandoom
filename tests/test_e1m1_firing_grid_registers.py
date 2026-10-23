"""Initialized grid registers, ABI restoration, and first-advance budget."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_grid_registers as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringGridRegisters')
HEADER+='open E1M1ThingGridRegisters (register)\nopen E1M1ThingList (Layout Image head run)\nopen E1M1ThingVisit (entry result)\n'
FULL=previous.ARGS+previous.HEAD+previous.DATA

class FiringGridRegistersTests(unittest.TestCase):
    lean=previous.FiringThingsTests.lean
    succeeds=previous.FiringThingsTests.succeeds
    rejects=previous.FiringThingsTests.rejects
    mutations=previous.FiringThingsTests.mutations

    def contract(self,module,name,args,section=False):
        source=previous.FiringThingsTests.contract(self,module,name,args,section)
        return source.replace(previous.HEADER,HEADER,1)

    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted()
        self.assertEqual(len(spec['units']),29)
        out=self.succeeds(proof.certificate(data,raw));proof.audit(out)
        for bad in [out.replace('Quot.sound','sorryAx'),out.replace('Quot.sound','native.ax'),
                    out+'extra',out.replace('before_advance','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_line_callback_restores_ebp_from_actual_saved_slot(self):
        self.mutations(self.contract('OriginalLineInterceptRegister','saved_prologue','s'),[
            ('=s.regs register','=s.regs 7'),('s.regs 4-savedOffset','s.regs 4-(24#32)')])
        self.mutations(self.contract('OriginalLineInterceptRegister','crossing_intercept',
            's trace line p v w h cursor savedSafe'),[
            ('(savedSafe : OriginalLineTail.RecordSafe s (s.regs 4-savedOffset))','(savedSafe : True)')])

    def test_thing_prologue_and_epilogue_use_distinct_counter_intercept_slots(self):
        self.mutations(self.contract('E1M1ThingGridRegisters','entry_saved','s x'),[
            ('=s.core.regs (register x)','=s.core.regs (register (!x))')])
        self.mutations(self.contract('E1M1ThingGridRegisters','finish_register','s x'),[
            ('s.core.regs 4+popOffset x','s.core.regs 4+popOffset (!x)')])

    def test_whole_list_register_transport_requires_capacity(self):
        self.mutations(self.contract('E1M1ThingGridRegisters','traversal_register',
            's trace resolve nodes ret layout image cursor pc r tracked capacity x'),[
            ('(capacity : r.collected.size+nodes.length≤128)','(capacity : r.collected.size≤128)'),
            ('(image : Image s.core.memory (s.core.regs 4) trace nodes ret)','(image : True)')])

    def test_initial_intercept_is_calculated_not_arbitrary(self):
        self.mutations(self.contract('E1M1FiringGridRegisters','initialized',previous.ARGS,True),[
            ('yout.2.1 yout.2.2','xout.2.1 xout.2.2'),
            ('core.regs 7=0','core.regs 7=1')])

    def test_first_advance_registers_derive_from_initial_contract(self):
        self.mutations(self.contract('E1M1FiringGridRegisters','before_advance',FULL+' room',True),[
            ('(room : c.ids.length+nodes.length≤128)','(room : True)'),
            ('out.core.regs 7=0','out.core.regs 7=1')])

    def test_continuous_prefix_counter_and_exit_are_joined(self):
        self.mutations(self.contract('E1M1FiringGridRegisters','execution',FULL+' room world dimension ids scene f',True),[
            ('steps≤427+','steps≤426+'),
            ('then 0 else 1','then 1 else 0'),
            ('then 0x2cafd else 0x2ca7f','then 0x2ca7f else 0x2cafd')])

if __name__=='__main__':unittest.main()

"""Complete first-cell numeric state and explicit address-only separation."""
import re
import unittest
from pathlib import Path
import test_e1m1_firing_things as previous
import verify_e1m1_firing_grid_state as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER=previous.HEADER.replace('import Doom.Proofs.E1M1FiringThings','import Doom.Proofs.E1M1FiringGridState')
HEADER+='open E1M1GridLocals (offsets address)\n'
FULL=previous.ARGS+previous.HEAD+previous.DATA+' locals'

class FiringGridStateTests(unittest.TestCase):
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
                    out+'extra',out.replace('before_observe','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))

    def test_stack_separation_requires_actual_local_offsets(self):
        self.mutations(self.contract('E1M1GridLocals','below','sp off member i'),[
            ('(member : off∈offsets)','(member : True)'),
            ('116+4*i.val','68+4*i.val')])

    def test_scans_require_heap_separation_not_reached_values(self):
        for name in ['scan_safe','thing_safe']:
            self.mutations(self.contract('E1M1GridLocals',name,'sp lines off member safe'),[
                ('(safe : Safe sp lines)','(safe : True)')])
        source=(ROOT/'Doom/Proofs/E1M1GridLocals.lean').read_text()
        fields=source.split('structure Safe',1)[1].split('/--',1)[0]
        for forbidden in ['load32','Outcome','Prefix','firstGrid']:
            self.assertNotIn(forbidden,fields)

    def test_endpoint_slots_and_initial_numeric_fields(self):
        self.mutations(self.contract('E1M1GridLocals','endpoints','s ox oy sx sy ex ey geometry'),[
            ('(20#32)','(16#32)'),('endBlockX.toBitVec','startBlockX.toBitVec')])
        self.mutations(self.contract('E1M1FiringGridState','of_ready','sp t p xout yout ready endX endY'),[
            ('(endX : load32 t.core.memory (t.core.regs 4+(20#32))=p.endBlockX.toBitVec)','(endX : True)')])

    def test_state_transport_needs_every_register_and_local(self):
        self.mutations(self.contract('E1M1FiringGridState','transport','t u regs locals'),[
            ('([1,5,6,7] : List (Fin 8))','([1,5,6] : List (Fin 8))'),
            ('(locals : ∀ off∈offsets, OriginalPathAdvance.localWord t off=OriginalPathAdvance.localWord u off)',
             '(locals : True)')])

    def test_full_list_preserves_locals_only_with_initial_layout(self):
        self.mutations(self.contract('E1M1FiringGridState','firing_local',FULL+' room off member',True),[
            ('(locals : E1M1GridLocals.Safe (s.regs 4) lines)','(locals : True)'),
            ('(room : c.ids.length+nodes.length≤128)','(room : True)')])

    def test_before_step_state_is_the_calculated_initial_state(self):
        self.mutations(self.contract('E1M1FiringGridState','before_observe',FULL+' room things scene',True),[
            ('initial (path thing angle ox oy) xout yout','initial (path thing angle ox oy) yout xout')])
        self.mutations(self.contract('E1M1FiringGridState','production_axis','p xout yout'),[
            ('xout.1 yout.1 yout.2.2 xout.2.2','xout.1 yout.1 xout.2.2 yout.2.2')])

    def test_joined_step_rejects_wrong_transition_and_exit(self):
        self.mutations(self.contract('E1M1FiringGridState','execution',FULL+' room world dimension ids scene f',True),[
            ('steps≤427+','steps≤426+'),
            ('E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)','initial (path thing angle ox oy) xout yout'),
            ('out.pc=E1M1PathAdvance.nextPc (initial (path thing angle ox oy) xout yout)','out.pc=0x2ca7f')])

if __name__=='__main__':unittest.main()

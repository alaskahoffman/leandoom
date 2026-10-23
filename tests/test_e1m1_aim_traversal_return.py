"""Guard the real return bytes, stack obligations, and the explicit RET 8 boundary."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_ordered_memory as prior
import verify_e1m1_aim_traversal_return as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimTraversalReturn\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight E1M1AimTraversalReturn.result
'''
class AimTraversalReturnTests(unittest.TestCase):
    lean=prior.AimOrderedMemoryTests.lean
    succeeds=prior.AimOrderedMemoryTests.succeeds
    rejects=prior.AimOrderedMemoryTests.rejects
    mutations=prior.AimOrderedMemoryTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  '+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),49)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimTraversalReturn.append','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_changed_cursor_store_and_stack_cleanup_bytes_rejected(self):
        for name,offset in [('interceptCode',7),('pathCode',2)]:
            module='OriginalTraversalReturn'
            text=(ROOT/f'Doom/Proofs/{module}.lean').read_text()
            items=text.split('def '+name+' : List UInt8 := [',1)[1].split(']',1)[0].split(',')
            source=HEADER+'example : (['+','.join(items)+'] : List UInt8)='+module+'.'+name+' := by decide\n'
            self.succeeds(source)
            items[offset]=str(int(items[offset],0)+1)
            self.rejects(HEADER+'example : (['+','.join(items)+'] : List UInt8)='+module+'.'+name+' := by decide\n')
    def test_execution_requires_the_real_saved_return_address(self):
        self.mutations(self.contract('E1M1AimTraversalReturn','execution','s exit safe address'),[
            ('(address : load32 s.core.memory (s.core.regs 4+20)=0x2cb0b)','(address : True)'),
            ('(safe : Apart (s.core.regs 4+20) 0x2c028)','(safe : True)'),
            ('(exit : s.pc=0x2c887 ∨ s.pc=0x2c88c)','(exit : True)')])
    def test_exact_cleanup_boundary_and_stack_adjustment(self):
        self.mutations(self.contract('E1M1AimTraversalReturn','layout','s'),[
            ('pc=0x2cb11','pc=0x2bbff'),('regs 4=s.core.regs 4+84','regs 4=s.core.regs 4+88'),
            ('then 1 else s.core.regs 0','then 0 else s.core.regs 0')])
        # This instruction is not silently accepted as an ordinary RET.
        self.succeeds(HEADER+'example : X86Routine.decodeAt [0xc2,8,0] 0=none := by decide\n')
    def test_saved_registers_require_separation_from_cursor_store(self):
        self.mutations(self.contract('E1M1AimTraversalReturn','saved_registers','s safe'),[
            ('(safe : ∀ off∈[(16#32),72,76,80], Apart (s.core.regs 4+off) 0x2c028)','(safe : True)'),
            ('regs 5=load32 s.core.memory (s.core.regs 4+72)','regs 5=load32 s.core.memory (s.core.regs 4+76)')])
    def test_next_return_address_requires_its_own_stack_word(self):
        self.mutations(self.contract('E1M1AimTraversalReturn','caller_address','s safe address'),[
            ('(address : load32 s.core.memory (s.core.regs 4+84)=0x2bbff)','(address : True)'),
            ('(safe : Apart (s.core.regs 4+84) 0x2c028)','(safe : True)')])
    def test_aim_value_still_requires_exit_relation_and_nonnull_pointers(self):
        self.mutations(self.contract('E1M1AimTraversalReturn','chosen','initial resolve s answer exit nonnull'),[
            ('(exit : E1M1AimHitMemory.Exit initial resolve s answer)','(exit : True)'),
            ('(nonnull : ∀ j<initial.size, resolve initial[j]!≠0)','(nonnull : True)'),
            ('OriginalAimQuery.chosen (Doom.Proofs.E1M1AimTraversalReturn.result s).core','(Doom.Proofs.E1M1AimTraversalReturn.result s).core.regs 0')])
    def test_loop_composition_keeps_endpoint_stack_obligations(self):
        self.mutations(self.contract('E1M1AimTraversalReturn','append','start finish steps run exit safe address'),[
            ('(safe : Apart (finish.core.regs 4+20) 0x2c028)','(safe : True)'),
            ('(address : load32 finish.core.memory (finish.core.regs 4+20)=0x2cb0b)','(address : True)'),
            ('n start (Doom.Proofs.E1M1AimTraversalReturn.result finish)','n start (Doom.Proofs.E1M1AimTraversalReturn.result start)')])
if __name__=='__main__':unittest.main()

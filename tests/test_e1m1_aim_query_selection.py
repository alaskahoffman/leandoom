"""Guard the continuous collection-to-initial-selection proof boundary."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_ordered_caller as prior
import verify_e1m1_aim_query_selection as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimQuerySelection\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32
'''
class AimQuerySelectionTests(unittest.TestCase):
    lean=prior.AimOrderedCallerTests.lean
    succeeds=prior.AimOrderedCallerTests.succeeds
    rejects=prior.AimOrderedCallerTests.rejects
    mutations=prior.AimOrderedCallerTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimQuerySelection.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_generic_scan_requires_matching_call_instructions(self):
        self.mutations(self.contract('E1M1ScanInterface','dispatch'),[
            ('(contains_call : ∀ pc, OriginalInterceptGate.program pc≠none →\n      program pc=OriginalInterceptGate.program pc)','(contains_call : True)'),
            ('(cursorSafe : Apart 0x2c028 (s.core.regs 4-4))','(cursorSafe : True)')])
    def test_return_is_created_by_real_call_even_at_wrapping_stack(self):
        self.mutations(self.contract('E1M1AimEntryFrame','return_word'),[
            ('(s.regs 4-4)=0x2cb0b','(s.regs 4-8)=0x2cb0b'),
            ('(s.regs 4-4)=0x2cb0b','(s.regs 4-4)=0x2bbff')])
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (stack : s.regs 4=0) (n : Nat) :
    load32 (E1M1InterceptSetup.result s n).core.memory 0xfffffffc=0x2cb0b := by
  simpa [stack] using E1M1AimEntryFrame.return_word s n
example : Apart (0xfffffffc#32) (0xffffffe4#32) :=
  E1M1AimEntryFrame.return_safe 0
''')
    def test_transport_needs_separation_from_all_stores(self):
        self.mutations(self.contract('E1M1AimEntryFrame','preserved'),[
            ('(safe : Doom.Proofs.E1M1AimEntryFrame.SafeWord (s.regs 4) a)','(safe : True)'),
            ('load32 out.core.memory a=load32 s.memory a','load32 out.core.memory a=load32 s.memory (a+4)')])
    def test_initial_selection_derives_shape_and_authentic_saved_return(self):
        source=self.contract('E1M1AimFirstSelection')
        for absent in ['(run :','(shape :','(position :','(first :','(selected :']:
            self.assertNotIn(absent,source)
        self.mutations(source,[
            ('(callback : OriginalInterceptSetup.callback s=0x2b760)','(callback : True)'),
            ('E1M1AimStackShape.Shape (s.regs 4-24) out','E1M1AimStackShape.Shape (s.regs 4-20) out'),
            ('load32 out.core.memory ((s.regs 4-24)+20)=0x2cb0b','load32 out.core.memory ((s.regs 4-24)+20)=0x2bbff')])
    def test_first_source_hit_keeps_zero_log_and_actual_query(self):
        self.mutations(self.contract('E1M1AimFirstSelection','source'),[
            ('(empty : original.visited=#[])','(empty : True)'),
            ('path.visited[0]! = original.collected[j]!','path.visited[1]! = original.collected[j]!')])
    def test_whole_query_requires_only_initial_callback_and_static_call_protection(self):
        source=self.contract('E1M1AimQuerySelection')
        for absent in ['(collected :','(out :','(run :','(frame :','(shape :','(limit :','(encoded :']:
            # Existential conclusions deliberately do bind collected/out.
            self.assertNotIn(absent,source.split(' :\n    let g :=')[0])
        self.mutations(source,[
            ('(argument : load32 s.memory (s.regs 4+8)=0x2b760)','(argument : True)'),
            ('(cursorCall : Apart 0x2c028 (q.sp-140))','(cursorCall : True)'),
            ('E1M1AimStackShape.Shape (q.sp-136) out','E1M1AimStackShape.Shape (q.sp-132) out')])
    def test_query_word_image_reaches_back_to_initial_memory(self):
        self.mutations(self.contract('E1M1AimQuerySelection'),[
            ('load32 out.core.memory a=load32 s.memory a','load32 out.core.memory a=load32 s.memory (a+4)'),
            ('load32 out.core.memory ((q.sp-136)+20)=0x2cb0b','load32 out.core.memory ((q.sp-136)+84)=0x2cb0b')])
if __name__=='__main__':unittest.main()

"""Regress authenticated controller entry, preserved outer stack, and caller return."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_three_calls as prior
import verify_e1m1_aim_controller_call as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimControllerCall\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimControllerCallTests(unittest.TestCase):
    lean=prior.AimThreeCallsTests.lean
    succeeds=prior.AimThreeCallsTests.succeeds
    rejects=prior.AimThreeCallsTests.rejects
    mutations=prior.AimThreeCallsTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimControllerCall.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_prologue_executes_exact_entry_and_call(self):
        self.mutations(self.contract('E1M1AimControllerEntry','execution'),[
            ('[] 9','[] 8'),('⟨s,f,0x2d7c0⟩','⟨s,f,0x2bb80⟩')])
    def test_first_request_needs_original_angle_and_stack_separation(self):
        self.mutations(self.contract('E1M1AimControllerEntry','arguments'),[
            ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
            ('(safe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b)','(safe : True)'),
            ('core.regs 3=0x04000000','core.regs 3=0x08000000')])
    def test_prologue_memory_preserves_only_separated_words(self):
        self.mutations(self.contract('E1M1AimControllerEntry','frame'),[
            ('(safe : ∀ b∈Doom.Proofs.E1M1AimControllerEntry.writes s, Apart a b)','(safe : True)')])
    def test_saved_register_order_and_outer_return_slot(self):
        self.mutations(self.contract('E1M1AimControllerEntry','saved'),[
            ('(s.regs 4-16)=s.regs 6','(s.regs 4-16)=s.regs 2'),
            ('load32 s.memory (s.regs 4)','load32 s.memory (s.regs 4-20)')])
    def test_epilogue_requires_preserved_slots(self):
        self.mutations(self.contract('E1M1AimControllerFrame','finished'),[
            ('(words : ∀ a∈Doom.Proofs.E1M1AimControllerFrame.slots s, load32 t.memory a=load32 s.memory a)','(words : True)'),
            ('(stack : t.regs 4=s.regs 4+4)','(stack : t.regs 4=s.regs 4)')])
    def test_slope_store_must_not_alias_saved_caller_words(self):
        for name in ['accepted','last']:
            with self.subTest(theorem=name):
                self.mutations(self.contract('E1M1AimControllerFrame',name),[
                    ('(safe : ∀ a∈Doom.Proofs.E1M1AimControllerFrame.slots s, Apart a 0x2c0c0)','(safe : True)')])
    def test_caller_return_restores_real_original_values(self):
        self.mutations(self.contract('E1M1AimControllerFrame','caller'),[
            ('out.pc=(load32 s.memory (s.regs 4)).toNat','out.pc=0x2d7d5'),
            ('out.core.regs 4=s.regs 4+4','out.core.regs 4=s.regs 4'),
            ('out.core.regs 6=s.regs 6','out.core.regs 6=s.regs 0')])
    def test_suffix_requires_all_five_caller_words_in_watch(self):
        source=self.contract('E1M1AimControllerCall','suffix')
        start=source.index('    (stackCovered :');end=source.index(' :\n    ∃ (selected',start)
        self.mutations(source,[(source[start:end],'    (stackCovered : True)')])
    def test_join_derives_first_request_and_resume(self):
        source=self.contract('E1M1AimControllerCall','execution')
        premises=source.split(' :\n    ∃ (selected')[0]
        self.assertNotIn('(controller :',premises);self.assertNotIn('(resume :',premises)
        self.assertIn('(E1M1AimControllerEntry.entry s f).core',premises)
        self.mutations(source,[
            ('(value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)','(value : True)'),
            ('⟨s,f,0x2d7c0⟩ out','⟨s,f,0x2bb80⟩ out')])
    def test_join_closes_slope_stack_return_and_saved_registers(self):
        source=self.contract('E1M1AimControllerCall','execution')
        self.assertIn('q.world.bulletAim shooter angle=.ok selected',source)
        self.mutations(source,[
            ('out.core.regs 4=s.regs 4+4','out.core.regs 4=s.regs 4+24'),
            ('out.core.regs 2=s.regs 2','out.core.regs 2=s.regs 0'),
            ('load32 out.core.memory 0x2c0c0=selected.slope.raw.toBitVec','load32 out.core.memory 0x2c0c0=0')])
    def test_stack_wrap_does_not_require_nonwrapping_address(self):
        self.succeeds(HEADER+'''
attribute [local semireducible] BitVec.add
example : (0#32)-20=0xffffffec := by decide
example : ((0#32)-20)+24=4 := by decide
example : Apart ((0#32)-16) ((0#32)-20) :=
  DeathStack.slots_apart 0 4 5 (by decide)
example (s : X86Memory.State) (f : Option Flags) (wrap : s.regs 4=0) :
    load32 (E1M1AimControllerEntry.entry s f).core.memory (0#32)=load32 s.memory 0 := by
  have saved := (E1M1AimControllerEntry.saved s f).2.2.2.2
  rw [wrap] at saved
  exact saved
''')
if __name__=='__main__':unittest.main()

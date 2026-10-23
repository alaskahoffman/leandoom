"""Guard stack/memory correspondence from ordered-loop entry through real return."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_scan_stack as prior
import verify_e1m1_aim_ordered_caller as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimOrderedCaller\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result
attribute [local irreducible] E1M1AimActorSkip.result E1M1AimActorReject.result E1M1AimActorBottomReject.result E1M1AimResume.result
'''
class AimOrderedCallerTests(unittest.TestCase):
    lean=prior.AimScanStackTests.lean
    succeeds=prior.AimScanStackTests.succeeds
    rejects=prior.AimScanStackTests.rejects
    mutations=prior.AimScanStackTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimOrderedStack.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_stack_shape_both_exits_and_wrapping_live_base(self):
        self.mutations(self.contract('E1M1AimStackShape','terminal'),[
            ('(pc : out.pc=0x2c887 ∨ out.pc=0x2c88c)','(pc : True)'),
            ('out.core.regs 4=base :=','out.core.regs 4=base-4 :=')])
        self.succeeds(HEADER+'''
example (out : X86Control.State) (pc : out.pc=0x2c887) (stack : out.core.regs 4=0) :
    E1M1AimStackShape.Shape 0 out := Or.inl ⟨Or.inl pc,stack⟩
example (out : X86Control.State) (pc : out.pc=0x2c88c) (stack : out.core.regs 4=0) :
    E1M1AimStackShape.Shape 0 out := E1M1AimStackShape.stopped _ _ pc stack
example (out : X86Control.State) (pc : out.pc=0x2b760) (stack : out.core.regs 4=0xfffffffc) :
    out.core.regs 4+4=0 :=
  E1M1AimStackShape.live 0 out (Or.inr ⟨pc,stack⟩) pc
''')
    def test_all_three_rejected_actor_cycles_need_their_actual_branches(self):
        for module,guard in [
            ('E1M1AimSkippedStack','(ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false)'),
            ('E1M1AimTopStack','(below : slope.raw<lower.raw)'),
            ('E1M1AimBottomStack','(above : upper.raw<bottomSlope.raw)')]:
            self.mutations(self.contract(module),[(guard,guard.split(' : ')[0]+' : True)'),
                ('Doom.Proofs.E1M1AimStackShape.Shape (s.regs 4+4) out','Doom.Proofs.E1M1AimStackShape.Shape (s.regs 4+8) out')])
    def test_unified_actor_callback_derives_memory_and_stack_from_catalog(self):
        source=self.contract('E1M1AimActorStack','catalog')
        self.assertNotIn('(shape :',source)
        self.mutations(source,[
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s scene shooter original.collected resolve who)','(catalog : True)'),
            ('Doom.Proofs.E1M1AimStackShape.Shape (s.regs 4+4) out','Doom.Proofs.E1M1AimStackShape.Shape (s.regs 4) out')])
    def test_open_line_requires_authentic_callback_slot(self):
        self.mutations(self.contract('E1M1AimOpenStack'),[
            ('(callback : load32 s.memory (s.regs 4+4)=0x2b760)','(callback : True)'),
            ('(slotMark : Apart (s.regs 4+4) (s.regs 3))','(slotMark : True)')])
    def test_portal_and_source_connections_keep_existing_representation(self):
        self.mutations(self.contract('E1M1AimPortalStack'),[
            ('(before : Doom.Proofs.E1M1AimTraversalInvariant.Persistent s initial work resolve portals distance z)','(before : True)')])
        self.mutations(self.contract('E1M1AimSynchronizedStack'),[
            ('(represented : Doom.Proofs.E1M1AimSourceCatalog.Represents scene result.collected portals)','(represented : True)')])
    def test_all_line_outcomes_need_coverage_and_keep_parent_base(self):
        self.mutations(self.contract('E1M1AimLineStack'),[
            ('(covered : Doom.Proofs.E1M1AimLineCoverage.Coverage result.collected walls portals)','(covered : True)'),
            ('Doom.Proofs.E1M1AimStackShape.Shape (s.regs 4+4) out','Doom.Proofs.E1M1AimStackShape.Shape (s.regs 4) out')])
    def test_complete_hit_preserves_both_word_and_stack_contracts(self):
        self.mutations(self.contract('E1M1AimHitStack'),[
            ('(arithmetic : Doom.Proofs.E1M1AimHitOutcome.Arithmetic scene shooter portals distance thing.shootHeight a j)','(arithmetic : True)'),
            ('(targetSafe : Doom.Proofs.E1M1AimMapFrame.StableWord s 0x2b9f8)','(targetSafe : True)')])
    def test_exhaustive_loop_proves_exit_esp_from_entry_shape(self):
        source=self.contract('E1M1AimOrderedStack')
        self.assertNotIn('(sequence :',source)
        self.assertNotIn('(finish :',source)
        self.mutations(source,[
            ('(shape : Doom.Proofs.E1M1AimStackShape.Shape base s)','(shape : True)'),
            ('out.core.regs 4=base ∧','out.core.regs 4=base-4 ∧')])
    def test_loop_retains_finite_descent_and_saved_word_preservation(self):
        self.mutations(self.contract('E1M1AimOrderedStack'),[
            ('(budget : fuel=original.collected.size-seen.length)','(budget : True)'),
            ('load32 out.core.memory addr=load32 s.core.memory addr','load32 out.core.memory (addr+4)=load32 s.core.memory addr')])
    def test_initial_loop_keeps_production_source_and_entry_protection(self):
        self.mutations(self.contract('E1M1AimOrderedStack','initial'),[
            ('(protect : ∀ addr∈watched, E1M1AimSavedWords.Protect s.core addr)','(protect : True)'),
            ('E1M1AimSource.afterPath scene shooter thing path distance=.ok answer','E1M1AimSource.afterPath scene shooter thing original distance=.ok answer')])
    def test_whole_ordered_return_has_no_endpoint_or_future_path_premises(self):
        source=self.contract('E1M1AimOrderedCaller')
        for absent in ['(image :','(finish :','(stack :','(run :','(sequence :','(position :']:
            self.assertNotIn(absent,source)
        self.mutations(source,[
            ('(first : load32 s.core.memory (base+20)=0x2cb0b)','(first : True)'),
            ('(second : load32 s.core.memory (base+84)=0x2bbff)','(second : True)'),
            ('(nonnull : ∀ j<original.collected.size, resolve original.collected[j]!≠0)','(nonnull : True)'),
            ('out.core.regs 0=answer.slope.raw.toBitVec','out.core.regs 0=0')])
if __name__=='__main__':unittest.main()

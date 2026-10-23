"""Guard entry-memory preservation without assuming reached return words."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_completed_return as prior
import verify_e1m1_aim_saved_caller as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimSavedCaller\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result E1M1AimActorReturn.result
'''
class AimSavedCallerTests(unittest.TestCase):
    lean=prior.AimCompletedReturnTests.lean
    succeeds=prior.AimCompletedReturnTests.succeeds
    rejects=prior.AimCompletedReturnTests.rejects
    mutations=prior.AimCompletedReturnTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimSavedWords.selected_frame','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_protection_includes_selected_target_and_slope_stores(self):
        source=HEADER+'''
example (s : X86Memory.State) (a : Word)
    (stable : E1M1AimMapFrame.StableWord s a)
    (target : Apart a 0x2b9f8) (slope : Apart a 0x2b9b4) :
    E1M1AimSavedWords.Protect s a := ⟨stable,target,slope⟩
'''
        self.mutations(source,[('(target : Apart a 0x2b9f8)','(target : True)'),
            ('(slope : Apart a 0x2b9b4)','(slope : True)')])
    def test_selected_branch_preserves_memory_under_actual_store_safety(self):
        self.mutations(self.contract('E1M1AimSavedWords','selected',proof.selected.STOP_ARGS),[
            ('(saveSafe : E1M1AimActorReturn.Safe s)','(saveSafe : True)'),
            ('Doom.Proofs.E1M1AimSavedWords.Preserved s out','Doom.Proofs.E1M1AimSavedWords.Preserved out.core ⟨s,f,0x2b760⟩')])
    def test_actor_cycle_needs_catalog(self):
        self.mutations(self.contract('E1M1AimActorSavedCycle','execution',proof.actor.EXEC_ARGS),[
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s scene shooter original.collected resolve who)','(catalog : True)')])
    def test_hit_requires_actual_source_representation(self):
        self.mutations(self.contract('E1M1AimHitSaved','execution',proof.ordered.HIT_ARGS),[
            ('(represented : Doom.Proofs.E1M1AimSourceCatalog.Represents scene original.collected portals)','(represented : True)'),
            ('(null : load32 s.memory (0x2b9f8#32)=0)','(null : True)')])
    def test_loop_carries_protection_and_preserves_fixed_addresses(self):
        self.mutations(self.contract('E1M1AimOrderedSaved','execution',proof.LOOP_ARGS),[
            ('∀ addr∈watched, E1M1AimSavedWords.Protect state addr','∀ addr∈watched, True'),
            ('load32 out.core.memory addr=load32 s.core.memory addr','load32 out.core.memory (addr+4)=load32 s.core.memory addr')])
    def test_initial_protection_and_image_bridge(self):
        self.mutations(self.contract('E1M1AimOrderedSaved','initial',proof.RESULT_ARGS),[
            ('(protect : ∀ addr∈watched, E1M1AimSavedWords.Protect s.core addr)','(protect : True)')])
        self.succeeds(HEADER+'''
example (start finish : X86Control.State) (base : Word)
    (kept : ∀ addr∈E1M1AimSavedCaller.words base,
      load32 finish.core.memory addr=load32 start.core.memory addr) :
    E1M1AimSavedCaller.Image start finish base := kept
''')
    def test_return_addresses_need_image_and_final_stack_position(self):
        self.mutations(self.contract('E1M1AimSavedCaller','addresses','start finish base image stack first second'),[
            ('(image : Doom.Proofs.E1M1AimSavedCaller.Image start finish base)','(image : True)'),
            ('(stack : finish.core.regs 4=base)','(stack : True)'),
            ('(base+84)=0x2bbff','(base+80)=0x2bbff')])
    def test_caller_restoration_uses_original_values_and_write_separation(self):
        self.mutations(self.contract('E1M1AimSavedCaller','restores','start finish base image stack protect'),[
            ('(protect : ∀ addr∈Doom.Proofs.E1M1AimSavedCaller.words base, Doom.Proofs.E1M1AimSavedWords.Protect start.core addr)','(protect : True)'),
            ('Doom.Proofs.E1M1AimSavedCaller.Restores start base','Doom.Proofs.E1M1AimSavedCaller.Restores finish base')])
    def test_complete_return_keeps_stack_and_source_obligations(self):
        source=self.contract('E1M1AimSavedCaller','execution',proof.CONTRACTS[-1][3])
        self.assertNotIn('(first : load32 finish',source)
        self.assertNotIn('(second : load32 finish',source)
        self.mutations(source,[
            ('(stack : finish.core.regs 4=base)','(stack : True)'),
            ('(exit : E1M1AimHitMemory.Exit initial resolve finish answer)','(exit : True)'),
            ('(nonnull : ∀ j<initial.size, resolve initial[j]!≠0)','(nonnull : True)')])
if __name__=='__main__':unittest.main()

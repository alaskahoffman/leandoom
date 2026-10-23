"""Guard null-target preservation and the original stale-slope return behavior."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_ordered_loop as prior
import verify_e1m1_aim_ordered_memory as proof
import verify_e1m1_aim_line_cycle as line_proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimOrderedMemory\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimOrderedMemoryTests(unittest.TestCase):
    lean=prior.AimOrderedLoopTests.lean
    succeeds=prior.AimOrderedLoopTests.succeeds
    rejects=prior.AimOrderedLoopTests.rejects
    mutations=prior.AimOrderedLoopTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimHitMemory.return_value','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_opening_protection_requires_real_read_separation(self):
        self.mutations(self.contract('E1M1AimNoTargetFrame','opening_safe','s a safe'),[
            ('(safe : E1M1AimRecordFrame.ReadSafe s a)','(safe : True)'),
            ('Apart a b','Apart (a+4) b')])
    def test_stopping_lines_keep_frame_under_actual_representation(self):
        self.mutations(self.contract('E1M1AimLineFrameCycle','execution',line_proof.EXEC_ARGS),[
            ('(catalog : E1M1AimWallCatalog.Catalog s result.collected resolve walls)','(catalog : True)'),
            ('(covered : Doom.Proofs.E1M1AimLineCoverage.Coverage result.collected walls portals)','(covered : True)'),
            ('Frame s out','Frame out.core out')])
    def test_hit_requires_initial_nullness_and_pointer_protection(self):
        self.mutations(self.contract('E1M1AimHitMemory','execution',proof.HIT_ARGS),[
            ('(null : load32 s.memory (0x2b9f8#32)=0)','(null : True)'),
            ('(targetSafe : Doom.Proofs.E1M1AimMapFrame.StableWord s 0x2b9f8)','(targetSafe : True)'),
            ('Outcome s scene shooter thing path original distance a seen visits resolve portals j out','Outcome s scene shooter thing path original distance a seen visits resolve portals (j+1) out')])
    def test_loop_requires_nullness_and_carries_live_protection(self):
        self.mutations(self.contract('E1M1AimOrderedMemory','execution',proof.LOOP_ARGS),[
            ('(null : load32 s.core.memory (0x2b9f8#32)=0)','(null : True)'),
            (' ∧ Doom.Proofs.E1M1AimMapFrame.StableWord state 0x2b9f8',' ∧ True')])
        self.mutations(self.contract('E1M1AimOrderedMemory','initial',proof.RESULT_ARGS),[
            ('(targetSafe : Doom.Proofs.E1M1AimMapFrame.StableWord s.core 0x2b9f8)','(targetSafe : True)'),
            ('(null : load32 s.core.memory (0x2b9f8#32)=0)','(null : True)')])
    def test_return_value_requires_nonnull_selected_pointers(self):
        self.mutations(self.contract('E1M1AimHitMemory','return_value',proof.RETURN_ARGS),[
            ('(nonnull : ∀ j<initial.size, resolve initial[j]!≠0)','(nonnull : True)'),
            ('(exit : Doom.Proofs.E1M1AimHitMemory.Exit initial resolve out answer)','(exit : True)'),
            ('OriginalAimQuery.chosen out.core=answer.slope.raw.toBitVec','OriginalAimQuery.chosen out.core=0')])
    def test_null_target_ignores_arbitrary_stale_slope(self):
        self.succeeds(HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State) (path : PathResult)
    (pc : out.pc=0x2c887) (null : load32 out.core.memory (0x2b9f8#32)=0) :
    OriginalAimQuery.chosen out.core=0 := by
  have exit : E1M1AimHitMemory.Exit initial resolve out {path} :=
    ⟨⟨Or.inl pc,by intro id target; cases target⟩,by intro _; exact ⟨null,rfl⟩⟩
  exact E1M1AimHitMemory.no_target_value initial resolve out _ exit rfl
''')
        self.rejects(HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State) (path : PathResult)
    (exit : E1M1AimHitMemory.Exit initial resolve out {path}) : load32 out.core.memory (0x2b9b4#32)=0 := by
  exact (exit.2 rfl).1
''')
    def test_absence_is_required_for_null_target_conclusion(self):
        source=HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State) (answer : AimResult)
    (exit : E1M1AimHitMemory.Exit initial resolve out answer) (absent : answer.target=none) :
    load32 out.core.memory (0x2b9f8#32)=0 ∧ answer.slope.raw.toBitVec=0 := by
  exact exit.2 absent
'''
        self.mutations(source,[('(absent : answer.target=none)','(absent : True)'),
                               ('load32 out.core.memory (0x2b9f8#32)=0 ∧','load32 out.core.memory (0x2b9b4#32)=0 ∧')])
if __name__=='__main__':unittest.main()

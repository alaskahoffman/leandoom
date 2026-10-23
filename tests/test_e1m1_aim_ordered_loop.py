"""Guard exhaustive dispatch, finite descent, and production-loop correspondence."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_mixed_exit as prior
import verify_e1m1_aim_ordered_loop as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimOrderedResult\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimOrderedLoopTests(unittest.TestCase):
    lean=prior.AimMixedExitTests.lean
    succeeds=prior.AimMixedExitTests.succeeds
    rejects=prior.AimMixedExitTests.rejects
    mutations=prior.AimMixedExitTests.mutations
    def contract(self,module,args):
        decl=proof.declaration(module,'execution').replace('theorem execution','example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.execution '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimOrderedLoop.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_callback_requires_line_coverage_and_guarded_arithmetic(self):
        self.mutations(self.contract('E1M1AimHitOutcome',proof.HIT_ARGS),[
            ('(covered : E1M1AimLineCoverage.Coverage original.collected walls portals)','(covered : True)'),
            ('(arithmetic : Doom.Proofs.E1M1AimHitOutcome.Arithmetic scene shooter portals distance thing.shootHeight a j)','(arithmetic : True)'),
            ('(wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)','(wallMap : True)'),
            ('n≤157+7*a.work.size','n≤156+7*a.work.size')])
    def test_loop_requires_actual_remaining_budget_and_history(self):
        self.mutations(self.contract('E1M1AimOrderedLoop',proof.LOOP_ARGS),[
            ('(budget : fuel=original.collected.size-seen.length)','(budget : True)'),
            ('(history : History original.collected a.work seen visits)','(history : True)'),
            ('n≤fuel*(157+7*original.collected.size)','n<fuel*(157+7*original.collected.size)')])
    def test_loop_keeps_arithmetic_and_memory_obligations_explicit(self):
        source=self.contract('E1M1AimOrderedLoop',proof.LOOP_ARGS)
        self.assertNotIn('(sequence :',source)
        self.assertNotIn('(done :',source)
        self.mutations(source,[
            ('(available : Doom.Proofs.E1M1AimOrderedLoop.Available scene shooter original.collected portals distance thing.shootHeight)','(available : True)'),
            ('(ready : Doom.Proofs.E1M1AimMixedExit.Ready s.core scene shooter original.collected a.work resolve who\n      (fun state => E1M1AimWallCatalog.Catalog state original.collected resolve walls))','(ready : True)'),
            ('(List.range\' seen.length (path.visited.size-seen.length))','(List.range\' (seen.length+1) (path.visited.size-(seen.length+1)))')])
    def test_initial_boundary_matches_production_after_path(self):
        self.mutations(self.contract('E1M1AimOrderedResult',proof.RESULT_ARGS),[
            ('(bottom : load32 s.core.memory (0x2c1e4#32)=aimBottomSlope.raw.toBitVec)','(bottom : True)'),
            ('(actors : Doom.Proofs.E1M1AimActorCatalog.Catalog s.core scene shooter original.collected resolve who)','(actors : True)'),
            ('(wallCatalog : E1M1AimWallCatalog.Catalog s.core original.collected resolve walls)','(wallCatalog : True)'),
            ('E1M1AimSource.afterPath scene shooter thing path distance=.ok answer','E1M1AimSource.afterPath scene shooter thing original distance=.ok answer')])
    def test_selected_zero_slope_still_requires_real_target_and_slope_stores(self):
        source=HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State)
    (answer : AimResult) (id : Nat) (exit : E1M1AimHitOutcome.Exit initial resolve out answer)
    (target : answer.target=some id) (zero : answer.slope.raw.toBitVec=0) :
    ∃ j<initial.size, initial[j]!.id=id ∧ load32 out.core.memory (0x2b9f8#32)=resolve initial[j]! ∧
      load32 out.core.memory (0x2b9b4#32)=0 := by
  obtain ⟨j,bound,same,pointer,slope⟩ := exit.2 id target
  exact ⟨j,bound,same,pointer,slope.trans zero⟩
'''
        self.mutations(source,[('load32 out.core.memory (0x2b9f8#32)=resolve initial[j]!','load32 out.core.memory (0x2b9f8#32)=0'),
                               ('(zero : answer.slope.raw.toBitVec=0)','(zero : True)')])
    def test_normal_exit_does_not_claim_no_target_globals_cleared(self):
        self.succeeds(HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State) (path : PathResult)
    (pc : out.pc=0x2c887) : E1M1AimHitOutcome.Exit initial resolve out {path} := by
  exact ⟨Or.inl pc,by intro id target; cases target⟩
''')
        self.rejects(HEADER+'''
example (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State) (path : PathResult)
    (exit : E1M1AimHitOutcome.Exit initial resolve out {path}) : load32 out.core.memory (0x2b9f8#32)=0 := by
  exact exit.2
''')
    def test_ignored_shooter_needs_no_division_equations(self):
        self.succeeds(HEADER+'''
example (scene : Scene) (shooter : Nat) (portals : Nat → Option E1M1AimCatalog.Portal)
    (distance z : Fixed) (a : E1M1AimPortalPrefix.Position) (j : Nat)
    (kind : a.work[j]!.isLine=false) (self : a.work[j]!.id=shooter) :
    Nonempty (E1M1AimHitOutcome.Arithmetic scene shooter portals distance z a j) := by
  refine ⟨⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,?_,?_,?_⟩⟩
  · intro line; rw [kind] at line; contradiction
  · intro _ different; exact False.elim (different self)
  · intro _ different; exact False.elim (different self)
''')
if __name__=='__main__':unittest.main()

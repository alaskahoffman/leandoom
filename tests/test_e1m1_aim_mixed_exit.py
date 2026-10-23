"""Guard normal and blocking exits after arbitrary continuing mixed prefixes."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_mixed_traversal as prior
import verify_e1m1_aim_mixed_exit as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimMixedBlocking\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimMixedExitTests(unittest.TestCase):
    lean=prior.AimMixedTraversalTests.lean
    succeeds=prior.AimMixedTraversalTests.succeeds
    rejects=prior.AimMixedTraversalTests.rejects
    mutations=prior.AimMixedTraversalTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimMixedExit.completed','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_boundary_step_preserves_history_and_real_frame(self):
        self.mutations(self.contract('E1M1AimMixedBoundary','execution',proof.STEP_ARGS),[
            ('(step : Doom.Proofs.E1M1AimMixedStep.Step scene shooter portals distance thing.shootHeight a j b)','(step : True)'),
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s scene shooter original.collected resolve who)','(catalog : True)'),
            ('History original.collected b.work (j::seen)','History original.collected b.work seen'),
            ('Frame s out','Frame out.core out')])
    def test_generic_transport_requires_the_preservation_law_and_initial_ready(self):
        source=self.contract('E1M1AimMixedExit','execution',proof.EXEC_ARGS)
        self.assertNotIn('(chosen :',source)
        self.mutations(source,[
            ('(ready : Doom.Proofs.E1M1AimMixedExit.Ready s.core scene shooter original.collected a.work resolve who Carry)','(ready : True)'),
            ('marked<128 → Carry before → Carry out.core','marked<128 → Carry before → True'),
            ('Ready out.core scene shooter original.collected final.work resolve who Carry','Ready out.core scene shooter original.collected final.work resolve who (fun _ => False)'),
            ('finalSeen.length=seen.length+count','finalSeen.length=seen.length+count+1')])
    def test_completed_requires_exhaustion_or_range_rejection(self):
        self.mutations(self.contract('E1M1AimMixedExit','completed',proof.DONE_ARGS),[
            ('(done : seen.length+count=original.collected.size ∨ ∃ best, Doom.Proofs.E1M1InterceptMinimum.minimum final.work=.ok best ∧ best.1>65536)','(done : True)'),
            ('out.pc=0x2c887','out.pc=0x2c88c'),
            ('best.1>65536','best.1≥65536'),
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s.core scene shooter original.collected resolve who)','(catalog : True)')])
    def test_closed_sector_requires_blocking_and_exact_stopped_visit(self):
        self.mutations(self.contract('E1M1AimMixedBlocking','closed',proof.CLOSED_ARGS),[
            ('(blocked : min (front p).ceiling.raw (back p).ceiling.raw ≤ max (front p).floor.raw (back p).floor.raw)','(blocked : True)'),
            ('(listed : portals j=some p)','(listed : True)'),
            ('(seen.length+count+1)','(seen.length+count)'),
            ('out.pc=0x2c88c','out.pc=0x2c887')])
    def test_clipped_window_requires_closed_window_and_division_correspondence(self):
        self.mutations(self.contract('E1M1AimMixedBlocking','stopped',proof.STOP_ARGS),[
            ('(distance*final.work[j]!.frac)=.ok floorSlope','(distance*final.work[j]!.frac)=.ok ceilingSlope'),
            ('(closed : ¬(Doom.Proofs.E1M1AimPortalPrefix.advance final j p distance floorSlope ceilingSlope).lower.raw <\n      (Doom.Proofs.E1M1AimPortalPrefix.advance final j p distance floorSlope ceilingSlope).upper.raw)','(closed : True)'),
            ('load32 out.core.memory (0x2c1e4#32)','load32 out.core.memory (0x2c1e8#32)')])
    def test_wall_stop_requires_initial_wall_catalog_source_map_and_actor_catalog(self):
        self.mutations(self.contract('E1M1AimMixedBlocking','wall',proof.WALL_ARGS),[
            ('(catalog : E1M1AimWallCatalog.Catalog s.core result.collected resolve walls)','(catalog : True)'),
            ('(wallMap : E1M1AimWallCatalog.Represents scene result.collected walls)','(wallMap : True)'),
            ('(actors : Doom.Proofs.E1M1AimActorCatalog.Catalog s.core scene shooter result.collected resolve who)','(actors : True)'),
            ('(listed : walls j)','(listed : True)'),
            ('+24, ∃ out','+23, ∃ out')])
    def test_no_hit_ready_does_not_require_a_fictitious_live_catalog(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (scene : Scene) (shooter : Nat) (initial work : Array Intercept)
    (resolve : Intercept → Word) (who : Word) (Carry : X86Memory.State → Prop)
    (best : E1M1InterceptMinimum.Best)
    (chosen : E1M1InterceptMinimum.minimum work=.ok best) (far : best.1>65536) :
    E1M1AimMixedExit.Ready s scene shooter initial work resolve who Carry := by
  intro fraction j admitted within
  have same := Except.ok.inj (chosen.symm.trans admitted)
  have eq : best.1=fraction := congrArg Prod.fst same
  exact False.elim (within (by simpa only [eq] using far))
''')
if __name__=='__main__':unittest.main()

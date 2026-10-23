"""Guard mixed traversal composition, progress and canonical final selection."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_actor_catalog as prior
import verify_e1m1_aim_mixed_traversal as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimMixedSelected\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimMixedTraversalTests(unittest.TestCase):
    lean=prior.AimActorCatalogTests.lean
    succeeds=prior.AimActorCatalogTests.succeeds
    rejects=prior.AimActorCatalogTests.rejects
    mutations=prior.AimActorCatalogTests.mutations
    def contract(self,module,name,args):
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+'namespace Doom.Proofs.'+module+'\n'+decl+' :=\n  '+module+'.'+name+' '+args+'\nend Doom.Proofs.'+module+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),47)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimMixedPrefix.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_step_requires_source_branch_catalog_and_admitted_successor(self):
        self.mutations(self.contract('E1M1AimMixedStep','execution',proof.STEP_ARGS),[
            ('(step : Doom.Proofs.E1M1AimMixedStep.Step scene shooter portals distance thing.shootHeight a j b)','(step : True)'),
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s scene shooter original.collected resolve who)','(catalog : True)'),
            ('(within : ¬nextFraction>65536)','(within : True)'),
            ('(chosen : Doom.Proofs.E1M1InterceptMinimum.minimum b.work=.ok (nextFraction,some k))','(chosen : True)')])
    def test_step_preserves_consumed_index_and_actual_source_suffix(self):
        self.mutations(self.contract('E1M1AimMixedStep','execution',proof.STEP_ARGS),[
            ('History original.collected b.work (j::seen)','History original.collected b.work (k::seen)'),
            ('(List.range\' (seen.length+1) (path.visited.size-(seen.length+1)))','(List.range\' seen.length (path.visited.size-seen.length))'),
            ('n≤157+7*a.work.size','n≤156+7*a.work.size')])
    def test_mixed_prefix_requires_sequence_history_and_entry_catalog(self):
        self.mutations(self.contract('E1M1AimMixedPrefix','execution',proof.PREFIX_ARGS),[
            ('(sequence : Doom.Proofs.E1M1AimMixedPrefix.Sequence scene shooter portals distance thing.shootHeight a final count)','(sequence : True)'),
            ('(history : History original.collected a.work seen visits)','(history : True)'),
            ('(catalog : Doom.Proofs.E1M1AimActorCatalog.Catalog s.core scene shooter original.collected resolve who)','(catalog : True)')])
    def test_prefix_retains_final_catalog_window_and_progress(self):
        self.mutations(self.contract('E1M1AimMixedPrefix','execution',proof.PREFIX_ARGS),[
            ('finalSeen.length=seen.length+count','finalSeen.length=seen.length+count+1'),
            ('Catalog out.core scene shooter original.collected resolve who','Catalog out.core scene (shooter+1) original.collected resolve who'),
            ('load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec','load32 out.core.memory (0x2c1e4#32)=final.upper.raw.toBitVec')])
    def test_capacity_is_derived_from_distinct_consumption(self):
        self.mutations(self.contract('E1M1AimMixedPrefix','capacity',proof.PREFIX_ARGS),[
            ('(history : History original.collected a.work seen visits)','(history : True)'),
            ('count≤original.collected.size-seen.length','count<original.collected.size-seen.length'),
            ('(within : ¬fraction>65536)','(within : True)')])
    def test_selected_hit_matches_store_and_source_index_after_mixed_prefix(self):
        self.mutations(self.contract('E1M1AimMixedSelected','selected',proof.SELECT_ARGS),[
            ('(bottomAdmitted : ¬final.upper.raw<bottomSlope.raw)','(bottomAdmitted : True)'),
            ('resolve original.collected[j]!','resolve original.collected[j+1]!'),
            ('(seen.length+count) final.work[j]!','(seen.length+count+1) final.work[j]!'),
            ('n≤count*(157+7*original.collected.size)+115','n≤count*(157+7*original.collected.size)+114')])
    def test_ignored_actor_then_portal_is_a_mixed_sequence(self):
        self.succeeds(HEADER+'''
open E1M1AimMixedStep E1M1AimMixedPrefix
open E1M1AimPortalPrefix (Position advance)
example (scene : Scene) (portals : Nat → Option E1M1AimCatalog.Portal) (distance z : Fixed)
    (a : Position) (j k : Nat) (p : E1M1AimCatalog.Portal) (fs cs : Fixed)
    (fraction nextFraction : Int32)
    (kind : a.work[j]!.isLine=false)
    (first : E1M1InterceptMinimum.minimum a.work=.ok (fraction,some j)) (near : ¬fraction>65536)
    (second : E1M1InterceptMinimum.minimum (skip a j).work=.ok (nextFraction,some k)) (nextNear : ¬nextFraction>65536)
    (portalStep : Step scene a.work[j]!.id portals distance z (skip a j) k
      (advance (skip a j) k p distance fs cs)) :
    Sequence scene a.work[j]!.id portals distance z a (advance (skip a j) k p distance fs cs) 2 := by
  have actorStep : Step scene a.work[j]!.id portals distance z a j (skip a j) :=
    Step.actor a j ⟨0⟩ ⟨0⟩ kind (by intro h; exact False.elim (h rfl))
      (by intro h; exact False.elim (h rfl))
      (by simp [E1M1AimActorDispatch.dispatch])
  exact Sequence.cons fraction j first near actorStep
    (Sequence.cons nextFraction k second nextNear portalStep (Sequence.nil _))
''')
if __name__=='__main__':unittest.main()

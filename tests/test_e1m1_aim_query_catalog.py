"""Guard the real initial-loop boundary and initial-memory catalog transport."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_query_selection as prior
import verify_e1m1_aim_query_catalog as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimQueryCatalog\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
attribute [local irreducible] E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result
'''
class AimQueryCatalogTests(unittest.TestCase):
    lean=prior.AimQuerySelectionTests.lean
    succeeds=prior.AimQuerySelectionTests.succeeds
    rejects=prior.AimQuerySelectionTests.rejects
    mutations=prior.AimQuerySelectionTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimQueryCatalog.catalogs','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_empty_boundary_needs_no_prior_callback_or_live_catalog(self):
        self.succeeds(HEADER+'''
example (scene : Scene) (shooter : Nat) (thing : SolidThing) (r : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option E1M1AimCatalog.Portal)
    (base : Word) (s : X86Control.State) (pc : s.pc=0x2c887)
    (stack : s.core.regs 4=base) (counter : s.core.regs 6=0xffffffff)
    (empty : r.visited=#[]) (noHits : r.collected.size=0) :
    E1M1AimActorBoundary.Boundary s.core scene shooter thing r r distance r.collected []
      resolve portals aimBottomSlope aimTopSlope #[] s := by
  apply E1M1AimInitialBoundary.boundary scene shooter thing r r distance resolve portals base s
    (Or.inl ⟨noHits,pc,counter⟩) (Or.inl ⟨Or.inl pc,stack⟩) empty
    (E1M1FirstIntercept.empty_tail r _ noHits)
  intro live
  omega
''')
        self.mutations(self.contract('E1M1AimInitialBoundary','boundary'),[
            ('(shape : E1M1AimStackShape.Shape base s)','(shape : True)'),
            ('(empty : original.visited=#[])','(empty : True)')])
    def test_initial_caller_uses_actual_outcome_but_keeps_live_invariants(self):
        source=self.contract('E1M1AimInitialCaller','execution')
        for absent in ['(origin :','(aligned :','(run :','(finish :']:
            self.assertNotIn(absent,source)
        self.mutations(source,[
            ('(outcome : E1M1AimFirstSelection.Outcome original.collected resolve base s)','(outcome : True)'),
            ('(persistent : s.pc=0x2b760 → E1M1AimTraversalInvariant.Persistent s.core\n      original.collected original.collected resolve portals distance thing.shootHeight)','(persistent : True)'),
            ('out.core.regs 0=answer.slope.raw.toBitVec','out.core.regs 0=0')])
    def test_byte_and_halfword_images_require_protected_addresses(self):
        for name in ['byte','half']:
            self.mutations(self.contract('E1M1AimEntryCatalog',name),[('(safe : P a)','(safe : True)')])
        self.mutations(self.contract('E1M1AimEntryCatalog','byte'),[('after a=before a','after a=before (a+1)')])
    def test_actor_and_wall_catalogs_require_read_coverage_and_matching_stack(self):
        self.mutations(self.contract('E1M1AimEntryCatalog','actors'),[
            ('(reads : Doom.Proofs.E1M1AimEntryCatalog.ActorReads initial resolve P)','(reads : True)'),
            ('(stack : t.regs 4=s.regs 4)','(stack : True)')])
        self.mutations(self.contract('E1M1AimEntryCatalog','walls'),[
            ('(reads : Doom.Proofs.E1M1AimEntryCatalog.WallReads initial resolve solid P)','(reads : True)')])
    def test_portal_image_includes_flags_side_index_pointers_and_heights(self):
        self.mutations(self.contract('E1M1AimEntryCatalog','portal_entry'),[
            ('(reads : ∀ a∈(line+16)::E1M1OpeningHeights.reads line p.front p.back, P a)','(reads : True)'),
            ('(entry : E1M1AimCatalog.Entry s hit line p)','(entry : True)')])
    def test_query_view_is_only_memory_and_static_stack_layout(self):
        self.succeeds(HEADER+'''
example (q : E1M1CellWalkInvariant.Context) (s : X86Memory.State) :
    (E1M1AimQueryCatalog.view q s).memory=s.memory ∧
    (E1M1AimQueryCatalog.view q s).regs 4=q.sp-140 := by
  simp [E1M1AimQueryCatalog.view,put,write]
''')
        self.mutations(self.contract('E1M1AimQueryCatalog','live_stack'),[
            ('(live : out.pc=0x2b760)','(live : True)'),
            ('out.core.regs 4=(Doom.Proofs.E1M1AimQueryCatalog.view q s).regs 4','out.core.regs 4=q.sp-136')])
    def test_query_catalog_transport_consumes_initial_memory_not_endpoint_images(self):
        self.mutations(self.contract('E1M1AimQueryCatalog','catalogs'),[
            ('(actorReads : E1M1AimEntryCatalog.ActorReads hits resolve (Doom.Proofs.E1M1AimQueryCatalog.Protected q s))','(actorReads : True)'),
            ('(actors : E1M1AimActorCatalog.Catalog (Doom.Proofs.E1M1AimQueryCatalog.view q s) scene shooter hits resolve who)','(actors : True)')])
    def test_five_query_globals_keep_initial_values_and_null_target(self):
        self.mutations(self.contract('E1M1AimQueryCatalog','globals'),[
            ('(null : load32 s.memory 0x2b9f8=0)','(null : True)'),
            ('load32 out.core.memory 0x2b9b8=distance.raw.toBitVec','load32 out.core.memory 0x2b9b8=z.raw.toBitVec'),
            ('load32 out.core.memory 0x2b9f8=0','load32 out.core.memory 0x2b9f8=1')])
if __name__=='__main__':unittest.main()

"""Guard setup-slot provenance and the derived live Persistent invariant."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_query_catalog as prior
import verify_e1m1_aim_query_persistent as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimQueryPersistent\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimQueryPersistentTests(unittest.TestCase):
    lean=prior.AimQueryCatalogTests.lean
    succeeds=prior.AimQueryCatalogTests.succeeds
    rejects=prior.AimQueryCatalogTests.rejects
    mutations=prior.AimQueryCatalogTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimEntryPersistent.persistent','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_first_scan_retains_slot_created_by_setup(self):
        source=self.contract('E1M1AimFirstSlot')
        self.assertNotIn('(slot :',source)
        self.mutations(source,[
            ('(callback : OriginalInterceptSetup.callback s=0x2b760)','(callback : True)'),
            ('load32 out.core.memory (s.regs 4-24)=0x2b760','load32 out.core.memory (s.regs 4-28)=0x2b760'),
            ('load32 out.core.memory (s.regs 4-24)=0x2b760','load32 out.core.memory (s.regs 4-24)=0x2c86d')])
    def test_query_slot_is_derived_from_initial_argument(self):
        source=self.contract('E1M1AimQuerySlot')
        self.assertNotIn('(slot :',source)
        self.mutations(source,[
            ('(argument : load32 s.memory (s.regs 4+8)=0x2b760)','(argument : True)'),
            ('load32 out.core.memory (q.sp-136)=0x2b760','load32 out.core.memory (q.sp-140)=0x2b760')])
    def test_layout_and_current_fraction_protection_need_actual_stack_and_selection(self):
        self.mutations(self.contract('E1M1AimEntryPersistent','layout'),[
            ('(sameStack : t.regs 4=s.regs 4)','(sameStack : True)')])
        self.mutations(self.contract('E1M1AimEntryPersistent','query_safe'),[
            ('(bounded : hits.size≤128)','(bounded : True)'),
            ('(stack : out.core.regs 4=s.regs 4)','(stack : True)')])
    def test_slot_mark_protection_comes_from_existing_setup_separation(self):
        self.mutations(self.contract('E1M1AimEntryPersistent','slot_marks'),[
            ('(separated : E1M1TraversalEntry.Protected q)','(separated : True)'),
            ('Apart (q.sp-136) (E1M1MinimumScan.address i)','Apart (E1M1MinimumScan.address i) (E1M1MinimumScan.address i)')])
    def test_real_resolver_stability_is_not_assumed(self):
        self.succeeds(self.contract('E1M1AimEntryPersistent','resolver'))
        self.succeeds(HEADER+'''
example (lines : Word) (objects : Nat → Word) (hit : Intercept) (thing : hit.isLine=false) :
    E1M1ThingFinish.resolve lines objects {hit with frac := ⟨2147483647⟩}=objects hit.id := by
  rw [E1M1AimEntryPersistent.resolver]
  simp [E1M1ThingFinish.resolve,thing]
example (lines : Word) (objects : Nat → Word) (hit : Intercept) (line : hit.isLine=true) :
    E1M1ThingFinish.resolve lines objects {hit with frac := ⟨2147483647⟩}=E1M1PathMap.resolve lines hit := by
  rw [E1M1AimEntryPersistent.resolver]
  simp [E1M1ThingFinish.resolve,line]
''')
    def test_persistent_assembly_needs_real_slot_and_initial_contracts(self):
        self.mutations(self.contract('E1M1AimEntryPersistent','persistent'),[
            ('(slot : load32 out.core.memory (q.sp-136)=0x2b760)','(slot : True)'),
            ('(initial : Doom.Proofs.E1M1AimEntryPersistent.Initial q s hits portals distance z)','(initial : True)')])
        source=(ROOT/'Doom/Proofs/E1M1AimEntryPersistent.lean').read_text()
        fields=source.split('structure Initial ',1)[1].split('/-- Rebase',1)[0]
        for absent in ['X86Control.State','callback :','resolver :','out.']:
            self.assertNotIn(absent,fields)
    def test_continuous_query_derives_live_invariant_without_endpoint_premises(self):
        source=self.contract('E1M1AimQueryPersistent')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(slot :','(persistent :','(frame :','(shape :','(run :']:
            self.assertNotIn(absent,args)
        self.mutations(source,[
            ('E1M1AimEntryPersistent.Initial q s after.collected portals distance z','True'),
            ('(out.pc=0x2b760 → E1M1AimTraversalInvariant.Persistent out.core after.collected after.collected',
             '(out.pc=0x2b760 → E1M1AimTraversalInvariant.Persistent out.core #[] after.collected')])
if __name__=='__main__':unittest.main()

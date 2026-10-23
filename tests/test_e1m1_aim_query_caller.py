"""Guard actual query/loop handoff, terminal returns, and caller-memory origin."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_query_persistent as prior
import verify_e1m1_aim_query_caller as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimQueryCaller\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimQueryCallerTests(unittest.TestCase):
    lean=prior.AimQueryPersistentTests.lean
    succeeds=prior.AimQueryPersistentTests.succeeds
    rejects=prior.AimQueryPersistentTests.rejects
    mutations=prior.AimQueryPersistentTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_authenticated_programs_and_transitive_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimReadyCaller.execution','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_returns_need_cursor_separation_and_exact_saved_addresses(self):
        source=self.contract('E1M1AimCallerCursor')
        self.assertNotIn('StableWord',source)
        self.mutations(source,[
            ('(protect : Doom.Proofs.E1M1AimCallerCursor.CursorSafe base)','(protect : True)'),
            ('(first : load32 start.core.memory (base+20)=0x2cb0b)','(first : True)'),
            ('(second : load32 start.core.memory (base+84)=0x2bbff)','(second : True)')])
    def test_callback_contracts_are_conditional_but_returns_still_protected(self):
        source=self.contract('E1M1AimReadyCaller')
        for name in ['actors','wallCatalog','targetSafe','protect']:
            self.assertIn('('+name+' : s.pc=0x2b760 →',source)
        self.mutations(source,[
            ('(cursorSafe : E1M1AimCallerCursor.CursorSafe base)','(cursorSafe : True)'),
            ('(actors : s.pc=0x2b760 → Doom.Proofs.E1M1AimActorCatalog.Catalog s.core',
             '(actors : s.pc=0x2c887 → Doom.Proofs.E1M1AimActorCatalog.Catalog s.core')])
    def test_restore_uses_query_entry_memory_not_only_middle_memory(self):
        self.mutations(self.contract('E1M1AimQueryCaller','restores'),[
            ('(frame : E1M1AimEntryCatalog.Image s.memory middle.core.memory',
             '(frame : E1M1AimEntryCatalog.Image s.memory s.memory'),
            ('E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-136) out',
             'E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-140) out')])
    def test_two_prefixes_share_exact_same_boundary(self):
        source=self.contract('E1M1AimQueryCaller')
        self.mutations(source,[
            ('E1M1AimCompletedReturn.program [] m middle out',
             'E1M1AimCompletedReturn.program [] m ⟨s,f,0x2c8a0⟩ out'),
            ('out.core.regs 0=answer.slope.raw.toBitVec','out.core.regs 1=answer.slope.raw.toBitVec'),
            ('q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok path',
             'q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok after')])
    def test_initial_only_contracts_and_explicit_source_obligations(self):
        source=self.contract('E1M1AimQueryCaller')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(middle :','(run :','(persistent :','(shape :','(frame :']:
            self.assertNotIn(absent,args)
        self.mutations(source,[
            ('Doom.Proofs.E1M1AimQueryCaller.Initial q s scene shooter thing after.collected distance portals walls who','True'),
            ('Doom.Proofs.E1M1AimQueryCaller.Source q scene shooter thing after path distance portals walls','True')])
        original=(ROOT/'Doom/Proofs/E1M1AimQueryCaller.lean').read_text()
        initial=original.split('structure Initial ',1)[1].split('/-- Remaining source-side',1)[0]
        for absent in ['X86Control.State','Prefix','middle.','out.']:
            self.assertNotIn(absent,initial)
if __name__=='__main__':unittest.main()

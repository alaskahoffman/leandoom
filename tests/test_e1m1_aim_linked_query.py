"""Guard compatible instruction union and the single continuous execution."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_query_caller as prior
import verify_e1m1_aim_linked_query as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimLinkedQuery\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimLinkedQueryTests(unittest.TestCase):
    lean=prior.AimQueryCallerTests.lean
    succeeds=prior.AimQueryCallerTests.succeeds
    rejects=prior.AimQueryCallerTests.rejects
    mutations=prior.AimQueryCallerTests.mutations
    def contract(self,module,name='execution'):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_inherits_both_authenticated_maps_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        certificate=proof.certificate(data,raw)
        self.assertIn('match Doom.Verification.ExtractedAimCompletedReturn.linked pc',certificate)
        self.assertIn('X86ReturnCleanup.embed Doom.Verification.ExtractedQueryDispatch.linked pc',certificate)
        output=self.succeeds(certificate);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimProgramLink.compatible','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_union_preserves_both_maps_and_actual_ret8(self):
        for name in ['compatible','contains_return','contains_query']:
            self.succeeds(self.contract('E1M1AimProgramLink',name))
        statement=HEADER+'''
example : E1M1AimProgramLink.program 0x2cb11=some (.retCleanup 8,3) := by decide
example : E1M1AimProgramLink.CompatibleAt 0xffffffff := E1M1AimProgramLink.compatible _
example (pc : Nat) : E1M1AimProgramLink.CompatibleAt pc := E1M1AimProgramLink.compatible pc
'''
        self.mutations(statement,[('.retCleanup 8,3','.retCleanup 0,3'),('.retCleanup 8,3','.retCleanup 8,1')])
    def test_join_requires_same_state_and_preserves_step_count(self):
        self.mutations(self.contract('E1M1AimProgramLink','append'),[
            ('E1M1AimCompletedReturn.program exits m middle finish','E1M1AimCompletedReturn.program exits m start finish'),
            ('exits (n+m) start finish','exits (n+m+1) start finish'),
            ('exits (n+m) start finish','exits (n+m) start middle')])
    def test_single_query_execution_has_no_middle_or_linkage_premises(self):
        source=self.contract('E1M1AimLinkedQuery')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['(out :','(middle :','(run :','(compatible :','(agree :']:
            self.assertNotIn(absent,args)
        result=source.split(' :\n    let g :=')[1].split(' :=\n')[0]
        self.assertEqual(result.count('X86ReturnCleanup.Prefix'),1)
        self.assertNotIn('X86CodeMemory.Prefix',result)
        self.mutations(source,[
            ('E1M1AimProgramLink.program [] n ⟨s,f,0x2c8a0⟩ out',
             'E1M1AimProgramLink.program [] n ⟨s,f,0x2bb80⟩ out'),
            ('out.core.regs 0=answer.slope.raw.toBitVec','out.core.regs 1=answer.slope.raw.toBitVec'),
            ('Doom.Proofs.E1M1AimQueryCaller.Initial q s scene shooter thing after.collected distance portals walls who','True')])
    def test_union_does_not_drop_a_completed_return(self):
        self.mutations(self.contract('E1M1AimProgramLink','contains_return'),[
            ('Doom.Proofs.E1M1AimProgramLink.program pc=E1M1AimCompletedReturn.program pc',
             'X86ReturnCleanup.embed E1M1FirstIntercept.program pc=E1M1AimCompletedReturn.program pc')])
if __name__=='__main__':unittest.main()

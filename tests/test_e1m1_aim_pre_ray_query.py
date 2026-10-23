"""Check that the complete aim theorem derives its traversal-memory contracts."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_entry_query as prior
import verify_e1m1_aim_pre_ray_query as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimPreRayQuery\n'+proof.HEADER+'''
attribute [local irreducible] load32 store32 SolidThing.shootHeight
'''
class AimPreRayQueryTests(unittest.TestCase):
    lean=prior.AimEntryQueryTests.lean
    succeeds=prior.AimEntryQueryTests.succeeds
    rejects=prior.AimEntryQueryTests.rejects
    mutations=prior.AimEntryQueryTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_complete_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimPreRayCatalog.remaining','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_image_requires_protection_before_and_after_setup(self):
        self.mutations(self.contract('E1M1AimPreRayMemory','image'),[
            ('(Doom.Proofs.E1M1AimPreRayMemory.Read q s)','(fun _ => True)'),
            ('(Doom.Proofs.E1M1AimPreRayMemory.Read q s)','(Doom.Proofs.E1M1AimPreRayMemory.Later q s)')])
        self.mutations(self.contract('E1M1AimPreRayMemory','later'),[
            ('(h : Doom.Proofs.E1M1AimPreRayMemory.Later q s a)','(h : True)')])
    def test_callback_uses_address_only_layout_but_requires_guard(self):
        self.mutations(self.contract('E1M1AimPreRayMemory','callback'),[
            ('(h : E1M1QueryCallback.CallbackSafe q (Doom.Proofs.E1M1AimPreRayMemory.layout s))','(h : True)')])
        self.succeeds(HEADER+'''
example (s : X86Memory.State) : (E1M1AimPreRayMemory.layout s).memory=s.memory := rfl
example (s : X86Memory.State) : (E1M1AimPreRayMemory.layout s).regs 4=s.regs 4-(28#32) := rfl
''')
    def test_payload_transports_data_and_guards_together(self):
        self.mutations(self.contract('E1M1AimPreRayMemory','payload'),[
            ('(data : E1M1QueryImages.Payload s.memory q c)','(data : True)'),
            ('(h : Doom.Proofs.E1M1AimPreRayMemory.PayloadSafe s q c)','(h : True)')])
    def test_shooter_is_written_from_eax_not_preserved(self):
        self.mutations(self.contract('E1M1AimPreRayCatalog','shooter'),[
            ('memory 0x2b9ac=s.regs 0','memory 0x2b9ac=s.regs 1'),
            ('memory 0x2b9ac=s.regs 0','memory 0x2b9ac=load32 s.memory 0x2b9ac')])
        source=(ROOT/'Doom/Proofs/E1M1AimPreRayCatalog.lean').read_text()
        structure=source.split('structure Initial',1)[1].split('/--',1)[0]
        self.assertIn('shooterReg : s.regs 0=who',structure)
        self.assertNotIn('shooterWord',structure)
        self.mutations(self.contract('E1M1AimPreRayCatalog','remaining'),[
            ('(h : Doom.Proofs.E1M1AimPreRayCatalog.Initial q s scene shooterId hits portals walls who)','(h : True)')])
    def test_full_query_has_no_computed_traversal_memory_premises(self):
        source=self.contract('E1M1AimPreRayQuery','execution')
        args=source.split(' :\n    let g :=')[0]
        for absent in ['traversal s','E1M1AimSetupCatalog.Remaining','(out :','(run :','(entry :']:
            self.assertNotIn(absent,args)
        self.assertIn('E1M1QueryImages.Payload s.memory q c',args)
        self.assertIn('E1M1AimPreRayCatalog.Initial q s q.world',args)
        self.assertIn('E1M1AimPreRayMemory.layout s',args)
        self.mutations(source,[
            ('E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe s q c','True'),
            ('E1M1AimPreRayCatalog.Initial q s q.world shooter after.collected portals walls who','True'),
            ('E1M1BulletAim.ProbeResult out.core answer','E1M1BulletAim.ProbeResult s answer')])
    def test_decision_keeps_original_return_word_and_source_target(self):
        source=self.contract('E1M1AimPreRayQuery','decision')
        args=source.split(' :\n    let g :=')[0]
        self.assertNotIn('traversal s',args)
        self.mutations(source,[
            ('(load32 s.memory (s.regs 4)).toNat','(load32 s.memory (s.regs 4+4)).toNat'),
            ('if answer.target.isSome then 0x2d81e','if answer.target.isSome then 0x2d7e4'),
            ('memory 0x2c0c0=answer.slope.raw.toBitVec','memory 0x2b9f8=answer.slope.raw.toBitVec')])
if __name__=='__main__':unittest.main()

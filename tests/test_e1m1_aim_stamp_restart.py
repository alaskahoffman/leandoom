"""Check stamp origins, real retry control and executed fresh next-probe setup."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_stamp_query as prior
import verify_e1m1_aim_stamp_restart as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimStampRestart\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add
'''
class AimStampRestartTests(unittest.TestCase):
    lean=prior.AimStampQueryTests.lean
    succeeds=prior.AimStampQueryTests.succeeds
    rejects=prior.AimStampQueryTests.rejects
    mutations=prior.AimStampQueryTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimStampRestart.retry_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_rebasing_requires_preserved_original_stamp_words(self):
        self.mutations(self.contract('E1M1AimStampOrigin','rebase'),[
            ('(kept : ∀ j<seen.size, load32 origin (OriginalLineVisits.stamp lines j)=\n      load32 before (OriginalLineVisits.stamp lines j))',
             '(kept : True)'),
            ('(image : E1M1AimStampImage.Image origin current lines epoch seen)','(image : True)')])
    def test_preray_origin_uses_actual_setup_contract_and_history_size(self):
        self.mutations(self.contract('E1M1AimStampOrigin','preray'),[
            ('(h : E1M1AimSetupEntry.Inputs q s thing angle distance)','(h : True)'),
            ('(size : seen.size=475)','(size : True)')])
    def test_complete_aim_call_carries_source_answer_and_unreset_history(self):
        source=self.contract('E1M1AimStampCall','execution')
        self.assertIn('⟨s,f,0x2bb80⟩ out',source)
        self.assertIn('q.world.aimLineAttack shooter angle distance=.ok answer',source)
        self.assertIn('E1M1AimCallerRegisters.Restores s out',source)
        self.mutations(source,[
            ('(history q (Array.replicate q.world.lines.size false) cells)',
             '(Array.replicate q.world.lines.size false)'),
            ('E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →',
             'E1M1AimStampImage.Fresh s.memory q.lines q.epoch 475 →')])
    def test_retry_is_controlled_by_target_presence_not_zero_slope(self):
        self.mutations(self.contract('E1M1AimStampCall','retry'),[
            ('(answer.target=none →','(answer.slope=Fixed.ofInt 0 →'),
            ('(resume : (load32 s.memory (s.regs 4)).toNat=if second then 0x2d7f8 else 0x2d7d5)',
             '(resume : True)')])
    def test_retry_writes_need_their_own_stamp_separation(self):
        self.mutations(self.contract('E1M1AimStampCall','retry'),[
            ('(stampRetry : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475, Apart a 0x2c0c0 ∧ Apart a (s.regs 4))',
             '(stampRetry : True)'),
            ('(stampProtected : ∀ a∈E1M1AimStampQuery.stampWords q.lines 475,\n      E1M1AimSavedWords.Protect (E1M1AimQueryCatalog.view q s) a)',
             '(stampProtected : True)')])
    def test_next_initialization_uses_inherited_image_and_future_freshness(self):
        self.mutations(self.contract('E1M1AimStampRestart','restart'),[
            ('(image : E1M1AimStampImage.Image s.memory next.core.memory q.lines q.epoch seen)','(image : True)'),
            ('(before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)',
             '(before : E1M1AimStampImage.Fresh s.memory q.lines q.epoch 475)'),
            ('(request : E1M1AimRetryRequest.Request second s next)','(request : True)')])
    def test_next_initialization_executes_the_original_axis_setup(self):
        source=self.contract('E1M1AimStampRestart','restart')
        self.assertIn('X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] (36+k) next out',source)
        self.mutations(source,[
            ('out.pc=0x2ca7f','out.pc=0x2c8a0'),
            ('''(okX : (path q thing.x thing.y (thing.attackEndpoint (Doom.Proofs.E1M1AimRetryGeometry.nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (Doom.Proofs.E1M1AimRetryGeometry.nextAngle second angle) (Fixed.ofInt 1024)).2).xStep=.ok nextX)''',
             '(okX : True)')])
    def test_restarted_history_uses_new_epoch_and_next_probe_origin(self):
        self.mutations(self.contract('E1M1AimStampRestart','restart'),[
            ('OriginalLineVisits.Represents out.core.memory q.lines (q.epoch+1)',
             'OriginalLineVisits.Represents out.core.memory q.lines q.epoch'),
            ('E1M1AimStampImage.Image next.core.memory out.core.memory',
             'E1M1AimStampImage.Image s.memory out.core.memory'),
            ('(Array.replicate 475 false)','(Array.replicate 475 true)')])
    def test_joined_prefix_reaches_next_cell_gate_without_assuming_its_image(self):
        source=self.contract('E1M1AimStampRestart','retry')
        args=source.split(' :\n    let g :=')[0]
        self.assertNotIn('(image :',args);self.assertNotIn('(before :',args)
        self.assertIn('((n+(4+(if second then 4 else 5)))+(36+k)) ⟨s,f,0x2bb80⟩ ready',source)
        self.assertIn('OriginalLineVisits.Represents ready.core.memory',source)
        self.mutations(source,[
            ('E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →',
             'E1M1AimStampImage.Fresh s.memory q.lines q.epoch 475 →'),
            ('(answer.target=none →','(answer.slope=Fixed.ofInt 0 →')])
if __name__=='__main__':unittest.main()

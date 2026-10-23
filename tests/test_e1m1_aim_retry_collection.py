"""Regress reconstructed retry entry and its actual generated collection loop."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_stamp_restart as prior
import verify_e1m1_aim_retry_collection as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimRetryCollection\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimRetryCollectionTests(unittest.TestCase):
    lean=prior.AimStampRestartTests.lean
    succeeds=prior.AimStampRestartTests.succeeds
    rejects=prior.AimStampRestartTests.rejects
    mutations=prior.AimStampRestartTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimRetryCollection.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_shared_layout_and_payload_guards_are_reused(self):
        self.mutations(self.contract('E1M1AimNextContext','common'),[
            ('(h : Common q)','(h : True)')])
        self.mutations(self.contract('E1M1AimNextContext','payload'),[
            ('(data : E1M1QueryImages.Payload s.memory q c)','(data : True)'),
            ('(safe : E1M1AimPreRayMemory.PayloadSafe s q c)','(safe : True)')])
    def test_next_input_needs_real_request_history_and_freshness(self):
        self.mutations(self.contract('E1M1AimNextContext','inputs'),[
            ('(request : E1M1AimRetryRequest.Request second s next)','(request : True)'),
            ('(image : E1M1AimStampImage.Image s.memory next.core.memory q.lines q.epoch seen)','(image : True)'),
            ('(before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)',
             '(before : E1M1AimStampImage.Fresh s.memory q.lines q.epoch 475)')])
    def test_next_entry_uses_changed_trace_epoch_and_retry_range(self):
        self.mutations(self.contract('E1M1AimNextContext','inputs'),[
            ('E1M1AimSetupEntry.Inputs (Doom.Proofs.E1M1AimNextContext.context q thing angle second) next.core thing',
             'E1M1AimSetupEntry.Inputs q next.core thing'),
            ('(size : seen.size=475)','(size : True)')])
        self.mutations(self.contract('E1M1AimNextContext','entry'),[
            ('(Fixed.ofInt 1024)','(Fixed.ofInt 2048)')])
    def test_next_collection_requires_its_route_metadata_and_capacity(self):
        self.mutations(self.contract('E1M1AimNextCollection','execution'),[
            ('(statics : ∀ c∈Doom.Proofs.E1M1AimNextContext.route q pick thing angle second nextX nextY, Admitted (Doom.Proofs.E1M1AimNextContext.context q thing angle second) c)',
             '(statics : True)'),
            ('(room : budget (Doom.Proofs.E1M1AimNextContext.context q thing angle second) (Doom.Proofs.E1M1AimNextContext.route q pick thing angle second nextX nextY)≤128)',
             '(room : True)')])
    def test_collection_reaches_ordered_setup_with_accumulated_stamps(self):
        self.mutations(self.contract('E1M1AimNextCollection','execution'),[
            ('out.pc=0x2cafd','out.pc=0x2ca7f'),
            ('E1M1AimStampImage.Image next.core.memory out.core.memory q.lines (q.epoch+1) (history cfg freshSeen cells)',
             'E1M1AimStampImage.Image next.core.memory out.core.memory q.lines (q.epoch+1) freshSeen')])
    def test_collection_retains_next_probe_origin_and_source_trace(self):
        self.mutations(self.contract('E1M1AimNextCollection','execution'),[
            ('E1M1AimStampImage.Image next.core.memory out.core.memory',
             'E1M1AimStampImage.Image s.memory out.core.memory'),
            ('E1M1LiveWalk.source q.world cfg.trace 64 g freshSeen',
             'E1M1LiveWalk.source q.world q.trace 64 g freshSeen')])
    def test_joined_prefix_has_no_assumed_reached_entry_or_collection(self):
        source=self.contract('E1M1AimRetryCollection','execution')
        args=source.split(' :\n    let g :=')[0]
        self.assertNotIn('(request :',args);self.assertNotIn('(image :',args)
        self.assertNotIn('(data : Doom.Proofs.E1M1AimRetryInputs.Prepared',args)
        self.assertIn('((n+(4+(if second then 4 else 5)))+m) ⟨s,f,0x2bb80⟩ collected',source)
        self.assertIn('q.world.aimLineAttack shooter angle distance=.ok answer',source)
        self.mutations(source,[
            ('(answer.target=none →','(answer.slope=Fixed.ofInt 0 →'),
            ('collected.pc=0x2cafd','collected.pc=0x2ca7f')])
    def test_joined_collection_uses_next_route_not_previous_pick(self):
        self.mutations(self.contract('E1M1AimRetryCollection','execution'),[
            ('let futureCells := Doom.Proofs.E1M1AimNextContext.route q nextPick thing angle second nextX nextY',
             'let futureCells := Doom.Proofs.E1M1AimNextContext.route q pick thing angle second nextX nextY')])
    def test_joined_next_capacity_and_original_freshness_remain_explicit(self):
        self.mutations(self.contract('E1M1AimRetryCollection','execution'),[
            ('(before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)','(before : True)'),
            ('(nextRoom : budget (Doom.Proofs.E1M1AimNextContext.context q thing angle second) (Doom.Proofs.E1M1AimNextContext.route q nextPick thing angle second nextX nextY)≤128)',
             '(nextRoom : True)')])
if __name__=='__main__':unittest.main()

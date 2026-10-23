"""Regress finite catalog transport and the continuous two-call aim execution."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_retry_collection as prior
import verify_e1m1_aim_retry_pair as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimRetryPair\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight SolidThing.attackEndpoint BitVec.add Doom.Proofs.E1M1LiveWalk.source
'''
class AimRetryPairTests(unittest.TestCase):
    lean=prior.AimRetryCollectionTests.lean
    succeeds=prior.AimRetryCollectionTests.succeeds
    rejects=prior.AimRetryCollectionTests.rejects
    mutations=prior.AimRetryCollectionTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimRetryPair.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_finite_reads_distinguish_actor_wall_and_portal_without_query_outputs(self):
        self.succeeds('import Doom.Proofs.E1M1AimRetryPair\n'+proof.HEADER+'''
set_option maxRecDepth 32768
def actor : Intercept := ⟨Fixed.ofInt 0,false,0⟩
def wall : Intercept := ⟨Fixed.ofInt 0,true,1⟩
def p : E1M1AimCatalog.Portal := ⟨0x4000,0x5000,0,0,0,0⟩
example : E1M1AimRetryCatalog.reads #[actor] (fun _ => 0x3000) (fun _ => none)=
    [0x3068,0x3014,0x3044] := by decide
example : E1M1AimRetryCatalog.reads #[wall] (fun _ => 0x6000) (fun _ => none)=
    [0x6010] := by decide
example : E1M1AimRetryCatalog.reads #[wall] (fun _ => 0x6000) (fun _ => some p)=
    [0x6010,0x6010] ++ E1M1OpeningHeights.reads 0x6000 0x4000 0x5000 := by decide
example : (E1M1AimRetryCatalog.reads #[actor,wall] (fun _ => 0x3000) (fun _ => some p)).all
    (fun a => !([(0x2b9ac#32),0x2b9b8,0x2b9a8,0x2c1e4,0x2c1e8,0x2b9f8].contains a))=true := by decide
''')
    def test_actor_wall_reads_require_correct_kind_and_valid_index(self):
        self.mutations(self.contract('E1M1AimRetryCatalog','actor_reads'),[
            ('(kind : hits[i]!.isLine=false)','(kind : hits[i]!.isLine=true)'),
            ('(hi : i<hits.size)','(hi : i≤hits.size)')])
        self.mutations(self.contract('E1M1AimRetryCatalog','wall_reads'),[
            ('(kind : hits[i]!.isLine=true)','(kind : True)')])
    def test_portal_read_requires_actual_catalog_entry(self):
        self.mutations(self.contract('E1M1AimRetryCatalog','portal_reads'),[
            ('(listed : portals i=some p)','(listed : True)'),
            ('(hi : i<hits.size)','(hi : i≤hits.size)')])
    def test_catalog_transfer_requires_memory_image_and_actual_shooter(self):
        self.mutations(self.contract('E1M1AimRetryCatalog','initial'),[
            ('(kept : ∀ a∈Doom.Proofs.E1M1AimRetryCatalog.reads hits (Doom.Proofs.E1M1ThingFinish.resolve q.lines q.objects) portals, load32 t.memory a=load32 s.memory a)',
             '(kept : True)'),
            ('(actor : t.regs 0=s.regs 0)','(actor : True)'),
            ('(stack : t.regs 4=s.regs 4)','(stack : True)')])
    def test_static_guards_require_restored_stack(self):
        for name in ['later','read','callback','saved']:
            with self.subTest(theorem=name):
                self.mutations(self.contract('E1M1AimRetryCatalog',name),[
                    ('(stack : t.regs 4=s.regs 4)','(stack : True)')])
    def test_next_call_derives_catalogs_from_original_memory(self):
        source=self.contract('E1M1AimNextCall','execution')
        self.assertIn(') s q.world shooter after.collected portals walls who',source)
        self.assertNotIn(') next.core q.world shooter after.collected portals walls who',source)
        self.mutations(source,[
            ('(kept : ∀ a∈watched, load32 next.core.memory a=load32 s.memory a)','(kept : True)'),
            ('(controller : s.regs 6=s.regs 0)','(controller : True)')])
    def test_next_answer_has_next_angle_and_full_original_return(self):
        self.mutations(self.contract('E1M1AimNextCall','execution'),[
            ('q.world.aimLineAttack shooter (Doom.Proofs.E1M1AimRetryGeometry.nextAngle second angle) (Fixed.ofInt 1024)=.ok answer',
             'q.world.aimLineAttack shooter angle (Fixed.ofInt 1024)=.ok answer'),
            ('E1M1AimCallerRegisters.Restores next.core out','E1M1AimCallerRegisters.Restores s out')])
    def test_next_stamp_image_keeps_actual_origin_and_accumulated_history(self):
        self.mutations(self.contract('E1M1AimNextCall','execution'),[
            ('E1M1AimStampImage.Image next.core.memory out.core.memory','E1M1AimStampImage.Image s.memory out.core.memory'),
            ('(history cfg (Array.replicate q.world.lines.size false) cells)',
             '(Array.replicate q.world.lines.size false)')])
    def test_joined_pair_uses_source_target_presence_and_exact_controller_return(self):
        source=self.contract('E1M1AimRetryPair','execution')
        self.assertIn('((n+(4+(if second then 4 else 5)))+m) ⟨s,f,0x2bb80⟩ finish',source)
        self.mutations(source,[
            ('(answer.target=none →','(answer.slope=Fixed.ofInt 0 →'),
            ('finish.pc=(if second then 0x2d819 else 0x2d7f8)',
             'finish.pc=(if second then 0x2d7f8 else 0x2d819)')])
    def test_joined_pair_requires_catalog_read_coverage(self):
        source=self.contract('E1M1AimRetryPair','execution')
        self.assertNotIn('(kept :',source);self.assertNotIn('(request :',source)
        self.mutations(source,[
            ('a∈(Doom.Proofs.E1M1AimRetryInputs.reads q s (Doom.Proofs.E1M1AimRetryGeometry.nextAngle second angle) (Doom.Proofs.E1M1AimNextContext.route q nextPick thing angle second nextX nextY) ++ extra)))',
             'True))')])
    def test_joined_pair_keeps_capacity_and_future_freshness_conditional(self):
        self.mutations(self.contract('E1M1AimRetryPair','execution'),[
            ('(before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475)','(before : True)'),
            ('(nextRoom : budget (Doom.Proofs.E1M1AimNextContext.context q thing angle second) (Doom.Proofs.E1M1AimNextContext.route q nextPick thing angle second nextX nextY)≤128)',
             '(nextRoom : True)')])
if __name__=='__main__':unittest.main()

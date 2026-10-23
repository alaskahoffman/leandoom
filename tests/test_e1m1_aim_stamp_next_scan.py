"""Regress exact visited-stamp values, scan composition and conditional freshness."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_retry_inputs as prior
import verify_e1m1_aim_stamp_next_scan as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimStampNextScan\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight BitVec.add
'''
class AimStampNextScanTests(unittest.TestCase):
    lean=prior.AimRetryInputsTests.lean
    succeeds=prior.AimRetryInputsTests.succeeds
    rejects=prior.AimRetryInputsTests.rejects
    mutations=prior.AimRetryInputsTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimStampScan.scan_image','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_original_image_and_transport_require_actual_values(self):
        self.mutations(self.contract('E1M1AimStampImage','start'),[
            ('(represented : Doom.Proofs.OriginalLineVisits.Represents m lines epoch seen)','(represented : True)')])
        self.mutations(self.contract('E1M1AimStampImage','transport'),[
            ('(counter : load32 n 0x13580=load32 m 0x13580)','(counter : True)'),
            ('(stamps : ∀ j<seen.size, load32 n (Doom.Proofs.OriginalLineVisits.stamp lines j)=load32 m (Doom.Proofs.OriginalLineVisits.stamp lines j))','(stamps : True)')])
    def test_both_marked_and_original_words_constrain_future_freshness(self):
        self.mutations(self.contract('E1M1AimStampImage','fresh'),[
            ('(different : epoch≠future)','(different : True)'),
            ('(before : Doom.Proofs.E1M1AimStampImage.Fresh origin lines future seen.size)','(before : True)')])
        self.mutations(self.contract('E1M1AimStampImage','next_fresh'),[
            ('Doom.Proofs.E1M1AimStampImage.Fresh origin lines (epoch+1) seen.size',
             'Doom.Proofs.E1M1AimStampImage.Fresh origin lines epoch seen.size')])
    def test_stamp_bounds_need_the_no_wrap_condition(self):
        self.mutations(self.contract('E1M1AimStampImage','bounded_fresh'),[
            ('(noWrap : epoch.toNat<2^32-1)','(noWrap : True)'),
            ('(noWrap : epoch.toNat<2^32-1)','(noWrap : epoch.toNat<2^32)'),
            ('(bounded : ∀ j<count, (load32 m (Doom.Proofs.OriginalLineVisits.stamp lines j)).toNat≤epoch.toNat)',
             '(bounded : True)')])
    def test_wraparound_can_collide_with_an_unvisited_zero_stamp(self):
        closedHeader='import Doom.Proofs.E1M1AimStampNextScan\n'+proof.HEADER
        self.succeeds(closedHeader+'''
example : ∃ m : Memory,
    OriginalLineVisits.Represents m 0x1000 0xffffffff #[false] ∧
    ¬ E1M1AimStampImage.Fresh m 0x1000 ((0xffffffff#32)+1) 1 := by
  let m := store32 (fun _ => 0) 0x13580 0xffffffff
  have counter : load32 m 0x13580=0xffffffff := load_store _ _ _
  have stampZero : load32 m (OriginalLineVisits.stamp 0x1000 0)=0 := by
    unfold m
    rw [load_store_apart _ _ _ _ (by unfold Apart OriginalLineVisits.stamp; decide)]
    rfl
  refine ⟨m,⟨counter,?_⟩,?_⟩
  · intro j hj
    have zero : j=0 := by change j<1 at hj; omega
    subst j
    rw [stampZero]
    decide
  · intro fresh
    apply fresh 0 (by decide)
    change load32 m (OriginalLineVisits.stamp 0x1000 0)=0
    exact stampZero
example : (0xffffffff#32)≠(0xffffffff#32)+1 := E1M1AimStampImage.successor_ne _
''')
    def test_real_initialization_needs_fresh_origin_and_write_guards(self):
        self.mutations(self.contract('E1M1AimStampImage','restart'),[
            ('(before : Doom.Proofs.E1M1AimStampImage.Fresh origin lines (epoch+1) seen.size)','(before : True)'),
            ('(epochSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x13580)','(epochSafe : True)'),
            ('(stampSafe : ∀ j<seen.size, E1M1PathMapSetup.Safe s (Doom.Proofs.OriginalLineVisits.stamp lines j))','(stampSafe : True)')])
    def test_step_and_early_stop_keep_the_actual_marked_prefix(self):
        self.mutations(self.contract('E1M1AimStampScan','step_image'),[
            ('(seen.set! (h.candidates i).id true)','(seen.set! (h.candidates i).id false)'),
            ('(represented : Doom.Proofs.OriginalLineVisits.Represents s.core.memory lines epoch seen)','(represented : True)')])
        self.mutations(self.contract('E1M1AimStampScan','scan_image'),[
            ('Doom.Proofs.OriginalLineVisits.markPrefix h.candidates out.visits i seen',
             'Doom.Proofs.OriginalLineVisits.markPrefix h.candidates k i seen')])
    def test_continuing_scan_and_sentinel_need_real_scan_premises(self):
        self.mutations(self.contract('E1M1AimStampScan','run_image'),[
            ('(keep : ∀ j, i≤j → j<i+k → (h.candidates j).crosses=true → (h.candidates j).Continues)',
             '(keep : True)')])
        self.mutations(self.contract('E1M1AimStampScan','finished_image'),[
            ('(tracked : OriginalLineCollection.Tracks initial base resolve r.collected n)','(tracked : True)')])
    def test_authenticated_scan_derives_image_and_conditional_freshness(self):
        source=self.contract('E1M1AimStampNextScan','from_entry')
        args=source.split(' :\n    let out :=')[0]
        self.assertNotIn('(image :',args)
        self.assertNotIn('(origin :',args)
        self.assertIn('X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program',source)
        self.mutations(source,[
            ('Doom.Proofs.E1M1AimStampImage.Fresh s.memory lines (epoch+1) seen.size →',
             'Doom.Proofs.E1M1AimStampImage.Fresh s.memory lines epoch seen.size →'),
            ('steps≤281*c.ids.length+7','steps≤281*c.ids.length+6'),
            ('(represented : Doom.Proofs.OriginalLineVisits.Represents s.memory lines epoch seen)','(represented : True)')])
if __name__=='__main__':unittest.main()

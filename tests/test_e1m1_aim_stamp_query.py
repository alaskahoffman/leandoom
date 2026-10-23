"""Regress the exact stamp image from query initialization through actual return."""
import re,unittest
from pathlib import Path
import test_e1m1_aim_stamp_walk as prior
import verify_e1m1_aim_stamp_query as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimStampQuery\n'+proof.HEADER+'''
set_option maxRecDepth 32768
attribute [local irreducible] load32 store32 SolidThing.shootHeight BitVec.add
'''
class AimStampQueryTests(unittest.TestCase):
    lean=prior.AimStampWalkTests.lean
    succeeds=prior.AimStampWalkTests.succeeds
    rejects=prior.AimStampWalkTests.rejects
    mutations=prior.AimStampWalkTests.mutations
    def contract(self,module,name):
        args=next(args for m,n,args in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_certificate_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();self.assertEqual(len(spec['units']),51)
        output=self.succeeds(proof.certificate(data,raw));proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',output.replace('AimStampQuery.execution_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
    def test_logged_cell_and_loop_keep_original_source_history(self):
        self.mutations(self.contract('E1M1AimStampLiveWalk','logged_one'),[
            ('(image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen)','(image : True)'),
            ('(scene : inside q c=true → E1M1CellLineSource.SceneLines q c)','(scene : True)')])
        self.mutations(self.contract('E1M1AimStampLiveWalk','logged'),[
            ('E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (history q seen cells)',
             'E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch seen')])
    def test_generated_route_needs_actual_numeric_counter(self):
        source=self.contract('E1M1AimStampLiveWalk','generated')
        self.assertNotIn('(follows :',source)
        self.mutations(source,[
            ('(legal : n<64)','(legal : True)'),
            ('(counter : (E1M1PathAdvance.observe s.core).count=BitVec.ofNat 32 n)','(counter : True)')])
        self.mutations(self.contract('E1M1AimStampLiveWalk','live'),[
            ('E1M1LiveWalk.source q.world q.trace (64-n) (E1M1PathAdvance.observe s.core) seen r=',
             'E1M1LiveWalk.source q.world q.trace 64 (E1M1PathAdvance.observe s.core) seen r=')])
    def test_initialization_uses_entry_words_and_the_incremented_epoch(self):
        self.mutations(self.contract('E1M1AimStampCollection','initialized_image'),[
            ('(entry : Entry q s sx sy ex ey)','(entry : True)'),
            ('q.lines q.epoch\n      (Array.replicate q.world.lines.size false)',
             'q.lines (q.epoch+1)\n      (Array.replicate q.world.lines.size false)')])
    def test_collection_derives_the_image_at_the_real_loop_exit(self):
        source=self.contract('E1M1AimStampCollection','collection')
        args=source.split(' :\n    let g :=')[0]
        self.assertNotIn('(image :',args);self.assertNotIn('(origin :',args)
        self.mutations(source,[
            ('out.pc=0x2cafd','out.pc=0x2ca7f'),
            ('E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q seen cells)',
             'E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch seen')])
    def test_word_set_covers_the_epoch_and_all_stamps(self):
        self.succeeds(HEADER+'''
example (lines : Word) (count : Nat) :
    (E1M1AimStampQuery.stampWords lines count).length=count+1 := by
  simp [E1M1AimStampQuery.stampWords]
example (lines : Word) (count j : Nat) (h : j<count) :
    OriginalLineVisits.stamp lines j∈E1M1AimStampQuery.stampWords lines count := by
  simp only [E1M1AimStampQuery.stampWords,List.mem_cons,List.mem_map,List.mem_range]
  exact Or.inr ⟨j,h,rfl⟩
example (lines : Word) : E1M1AimStampQuery.stampWords lines 0=[0x13580] := rfl
''')
    def test_transport_requires_complete_word_frame_and_matching_count(self):
        self.mutations(self.contract('E1M1AimStampQuery','transport'),[
            ('(size : seen.size=count)','(size : True)'),
            ('(kept : ∀ a∈Doom.Proofs.E1M1AimStampQuery.stampWords lines count, load32 n a=load32 m a)',
             '(kept : True)')])
    def test_selection_requires_its_own_stamp_write_guards(self):
        self.mutations(self.contract('E1M1AimStampQuery','selection'),[
            ('(stampSafe : ∀ a∈Doom.Proofs.E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)',
             '(stampSafe : True)'),
            ('(argument : load32 s.memory (s.regs 4+8)=0x2b760)',
             '(argument : load32 s.memory (s.regs 4+8)=0x2b761)')])
    def test_callback_invariant_does_not_replace_exact_stamp_image(self):
        self.mutations(self.contract('E1M1AimStampQuery','persistent'),[
            ('E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q seen cells)',
             'E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch seen'),
            ('(stampSafe : ∀ a∈Doom.Proofs.E1M1AimStampQuery.stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)',
             '(stampSafe : True)')])
    def test_ordered_aim_and_return_preserve_the_same_image(self):
        source=self.contract('E1M1AimStampQuery','execution')
        self.assertIn('X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program',source)
        self.assertIn('E1M1AimSavedCaller.Restores',source)
        self.assertIn('E1M1AimSource.afterPath',source)
        self.mutations(source,[
            ('(stampProtected : ∀ a∈Doom.Proofs.E1M1AimStampQuery.stampWords q.lines 475, E1M1AimSavedWords.Protect (Doom.Proofs.E1M1AimQueryCatalog.view q s) a)',
             '(stampProtected : True)'),
            ('(history q (Array.replicate q.world.lines.size false) cells)',
             '(Array.replicate q.world.lines.size false)')])
    def test_final_freshness_still_requires_the_future_epoch(self):
        self.mutations(self.contract('E1M1AimStampQuery','execution'),[
            ('E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →',
             'E1M1AimStampImage.Fresh s.memory q.lines q.epoch 475 →')])
if __name__=='__main__':unittest.main()

"""The real cache branch is selected by the preserved original owner cell."""
import sys,unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_cache_call as prior
ROOT=prior.ROOT
HEADER='''import Doom.Proofs.E1M1AimCacheDispatch
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWordFill (Entry32Safe OutputSafe)
open E1M1AimCacheDispatch
'''
class AimCacheDispatchTests(unittest.TestCase):
    lean=prior.AimCacheCallTests.lean
    succeeds=prior.AimCacheCallTests.succeeds
    rejects=prior.AimCacheCallTests.rejects
    def test_original_selected_dispatch_not_assumed_hit(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimCacheDispatch.lean').exists(),'actual cache dispatcher proof missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v)
    (inputs : CacheInitial s v cache) :
    ∃ h<8, (∃ n≤5317, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (dispatched s h cache)) ∧
      (dispatched s h cache).pc=(if load32 s.memory (cache+36)=0 then 0x38d35 else 0x38cab) ∧
      (dispatched s h cache).core.regs 3=cache+36 ∧
      (dispatched s h cache).core.regs 7=load32 s.memory (cache+36) :=
  entry_execution s f table cache initial v heap frame aligned safe inputs
''')
    def test_miss_reaches_real_allocator_from_original_directory(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v)
    (inputs : CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16)) :
    ∃ h<8, (∃ n≤5331, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (requested s h cache)) ∧
      (requested s h cache).pc=0x39690 ∧
      (requested s h cache).core.regs 0=19440 ∧
      (requested s h cache).core.regs 2=1 ∧
      (requested s h cache).core.regs 3=cache+36 ∧
      load32 (requested s h cache).core.memory ((requested s h cache).core.regs 4)=0x38d41 :=
  miss_entry_execution s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
''')
    def test_real_hit_signature_and_tag_call(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v)
    (inputs : CacheInitial s v cache) (hit : load32 s.memory (cache+36)≠0)
    (magic : load32 s.memory (load32 s.memory (cache+36)-12)=0x1d4a11)
    (magicSafe : E1M1AimCacheCall.ReadSafe s v (load32 s.memory (cache+36)-12)) :
    ∃ h<8, (∃ n≤5322, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (tagRequested s h cache)) ∧
      (tagRequested s h cache).pc=0x399b0 ∧
      (tagRequested s h cache).core.regs 0=load32 s.memory (cache+36) ∧
      (tagRequested s h cache).core.regs 2=1 ∧
      load32 (tagRequested s h cache).core.memory ((tagRequested s h cache).core.regs 4)=0x38cd3 :=
  hit_entry_execution s f table cache initial v heap frame aligned safe inputs hit magic magicSafe
''')
    def test_request_zero_output_and_original_word_frame(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v) :
    (∀ j<11664, (dispatched s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0) ∧
    (∀ j<11664, (requested s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0) ∧
    (∀ j<11664, (tagRequested s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0) :=
  output_preserved s f table cache initial v heap frame h small safe
''')
    def test_previous_allocation_metadata_is_preserved(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v) (a : Word)
    (nested : E1M1AimSideMemset.EntrySafe s a) (output : OutputSafe s v a) :
    load32 (requested s h cache).core.memory a=load32 (E1M1AimSideAllocate.allocated s).core.memory a :=
  request_allocation_frame s f table cache initial v heap frame h small safe a nested output
''')
    def test_cumulative_certificate_and_negative_binding(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_cache_call.py').exists(),'cache certificate missing')
        import verify_e1m1_aim_cache_call as p,copy
        text=p.certificate(); output=self.succeeds(text); p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('miss_entry_execution_checked','missing',1)]:
            with self.assertRaises(ValueError): p.audit(bad)
        for old,new in [('0xba,0x1,0x0,0x0,0x0,0x89,0xc8','0xba,0x2,0x0,0x0,0x0,0x89,0xc8'),
                        ('0x85,0xff,0xf,0x85,0x76','0x85,0xff,0xf,0x84,0x76'),
                        ('0x81,0x7f,0xf4,0x11','0x81,0x7f,0xf4,0x12')]:
            self.assertIn(old,text); self.rejects(text.replace(old,new,1))
        _,units,_=p.cache_data()
        for field in ['file_offset','code_offset']:
            bad=copy.deepcopy(units); bad['cache'][field]=hex(int(bad['cache'][field],16)+1)
            with self.assertRaises(ValueError): p.cache_data({'units':bad})
        bad=copy.deepcopy(units);bad['hit']['relocations'][0]['target']='0x23a85'
        with self.assertRaises(ValueError): p.cache_data({'units':bad})
    def test_initial_guards_cannot_be_erased(self):
        import verify_e1m1_aim_cache_call as p
        for module,name,guard in [
            ('E1M1AimCacheCall','entry_execution','(safe : Entry32Safe s v)'),
            ('E1M1AimCacheDispatch','miss_entry_execution','(miss : load32 s.memory (cache+36)=0)'),
            ('E1M1AimCacheDispatch','hit_entry_execution','(hit : load32 s.memory (cache+36)≠0)'),
            ('E1M1AimCacheDispatch','hit_execution','(magic : load32 s.memory (raw-12)=0x1d4a11)'),
            ('E1M1AimCacheDispatch','request_allocation_frame','(output : OutputSafe s v a)'),
            ('E1M1AimCacheCall','entry_frame','(readSafe : Doom.Proofs.E1M1AimCacheCall.ReadSafe s v a)')]:
            decl,args=p.extraction.contract(module,name)
            header=HEADER+'open E1M1AimCacheCall (ReadSafe)\n'
            text=header+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds(text); self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
if __name__=='__main__': unittest.main()

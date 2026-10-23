"""The next allocator view is produced, never assumed at a reached state."""
import sys, unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_cache_call as prior
ROOT=prior.ROOT
HEADER='''import Doom.Proofs.E1M1AimCacheHeap
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimCacheHeap
'''
class AimCacheHeapTests(unittest.TestCase):
    lean=prior.AimCacheCallTests.lean
    succeeds=prior.AimCacheCallTests.succeeds
    rejects=prior.AimCacheCallTests.rejects
    def test_next_heap_is_derived_from_original_and_side_effects(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimCacheHeap.lean').exists(),'produced next heap derivation missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : History s v nextSize nextNext)
    (kept : ∀ w∈(nextView v nextSize nextNext).words,
      E1M1AimSideMemset.EntrySafe s w.1 ∧ E1M1AimWordFill.OutputSafe s v w.1) :
    (nextView v nextSize nextNext).Holds (E1M1AimCacheDispatch.requested s h cache).core.memory := by
  exact requested_view s f table cache initial v heap frame h small safe nextSize nextNext history kept
''')
    def test_real_owned_allocator_return_is_connected(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimCacheAllocate.lean').exists(),'actual owned raw allocation missing')
        self.succeeds('''import Doom.Proofs.E1M1AimCacheAllocate
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimCacheAllocate
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : E1M1AimWordFill.Entry32Safe s v)
    (inputs : E1M1AimCacheDispatch.CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16))
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : Conditions s v cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5400, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (allocated s h cache)) ∧
      (allocated s h cache).pc=0x38d41 ∧
      (allocated s h cache).core.regs 0=(E1M1AimCacheHeap.nextView v nextSize nextNext).block+24 ∧
      (allocated s h cache).core.regs 4=s.regs 4-52 ∧
      load32 (allocated s h cache).core.memory (cache+36)=
        (E1M1AimCacheHeap.nextView v nextSize nextNext).block+24 := by
  exact entry_execution s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
    nextSize nextNext history conditions
''')
    def test_real_read_call_uses_published_owned_pointer(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimCacheRead.lean').exists(),'actual cache read CALL missing')
        self.succeeds('''import Doom.Proofs.E1M1AimCacheRead
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimCacheRead
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : E1M1AimWordFill.Entry32Safe s v)
    (inputs : E1M1AimCacheDispatch.CacheInitial s v cache) (miss : load32 s.memory (cache+36)=0)
    (pointerSafe : E1M1AimCacheCall.ReadSafe s v 0x74fa4)
    (lengthSafe : E1M1AimCacheCall.ReadSafe s v (180+table+16))
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (readSafe : ReadConditions s v cache nextSize nextNext) :
    ∃ h<8, (∃ n≤5404, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (readCalled s h cache)) ∧
      (readCalled s h cache).pc=0x38bf0 ∧ (readCalled s h cache).core.regs 0=9 ∧
      (readCalled s h cache).core.regs 2=(E1M1AimCacheHeap.nextView v nextSize nextNext).block+24 ∧
      (readCalled s h cache).core.regs 4=s.regs 4-56 ∧
      load32 (readCalled s h cache).core.memory (s.regs 4-56)=0x38d50 := by
  exact entry_execution s f table cache initial v heap frame aligned safe inputs miss pointerSafe lengthSafe
    nextSize nextNext history conditions readSafe
''')
    def test_new_writes_preserve_all_side_zero_bytes(self):
        self.succeeds('''import Doom.Proofs.E1M1AimCacheRead
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimCacheRead
example (s : X86Memory.State) (f : Option Flags) (table cache : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : E1M1AimWordFill.Entry32Safe s v)
    (nextSize nextNext : Word) (history : E1M1AimCacheHeap.History s v nextSize nextNext)
    (conditions : E1M1AimCacheAllocate.Conditions s v cache nextSize nextNext)
    (output : ∀ j<11664, ByteSafe (v.block+24+BitVec.ofNat 32 j)
      (laterAddresses s (E1M1AimCacheHeap.nextView v nextSize nextNext) cache)) :
    ∀ j<11664, (readCalled s h cache).core.memory (v.block+24+BitVec.ofNat 32 j)=0 := by
  exact output_preserved s f table cache initial v heap frame h small safe nextSize nextNext history conditions output
''')
    def test_produced_metadata_and_count_frames(self):
        self.succeeds('''import Doom.Proofs.E1M1AimCacheRead
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimCacheRead
#check produced_frame
#check published_word
''')
    def test_capacity_and_both_original_successor_cases(self):
        self.succeeds(HEADER+'''
def fixture (size : Word) : OriginalGroupHeap.View := ⟨0x610800,0x620000,0x630000,2,0x630000,size,0x640000⟩
example : (nextView (fixture (11688+64)) 19464 0x650000).block=0x640000 := by decide +kernel
example : (nextView (fixture (11688+19464)) 0 0).block=0x620000+11688 := by decide +kernel
example : (nextView (fixture (11688+19464)) 0 0).size=19464 := by decide +kernel
example : (OriginalGroupMallocEntry.rounded 11664).toInt≤(11688+65 : Word).toInt ∧
    ¬(OriginalGroupMallocEntry.rounded 19440).toInt≤(nextView (fixture (11688+65)) 0 0).size.toInt := by decide +kernel
''')
    def test_certificate_and_negative_guards(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_cache_heap.py').exists(),'cache heap cumulative verifier missing')
        import verify_e1m1_aim_cache_heap as p
        text=p.certificate(); output=self.succeeds(text); p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('requested_view_checked','missing',1)]:
            with self.assertRaises(ValueError): p.audit(bad)
        for old,new in [('0xc7,0x43,0x4,0x2','0xc7,0x43,0x4,0x3'),('0x89,0x7b,0x4','0x89,0x7b,0x8'),
                        ('0x8b,0x14,0x6,0x89,0xc8','0x8b,0x14,0x6,0x89,0xd0')]:
            self.assertIn(old,text);self.rejects(text.replace(old,new,1))
        for module,name,guard in [
            ('E1M1AimCacheHeap','requested_view','history'),
            ('E1M1AimCacheAllocate','local_execution','c'),
            ('E1M1AimCacheAllocate','entry_execution','conditions'),
            ('E1M1AimCacheRead','entry_execution','readSafe'),
            ('E1M1AimCacheRead','output_preserved','output')]:
            decl,args=p.contract(module,name)
            import re
            prefix=p.HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds('import Doom.Proofs.E1M1AimCacheRead\n'+prefix)
            # Replace the entire balanced binder type, not a textual subset.
            start=prefix.index('('+guard+' :'); depth=1; end=start+1
            while depth:
                depth += (prefix[end]=='(')-(prefix[end]==')'); end+=1
            bad=prefix[:start]+'('+guard+' : True)'+prefix[end:]
            self.rejects('import Doom.Proofs.E1M1AimCacheRead\n'+bad)
if __name__=='__main__': unittest.main()

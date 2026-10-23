"""Actual post-memset cache CALL, not an assumed cache image."""
import sys, unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_word_aligned as prior
ROOT=prior.ROOT
HEADER='''import Doom.Proofs.E1M1AimCacheCall
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWordFill (Entry32Safe OutputSafe)
open E1M1AimCacheCall
'''
class AimCacheCallTests(unittest.TestCase):
    lean=prior.AimWordAlignedTests.lean
    succeeds=prior.AimWordAlignedTests.succeeds
    rejects=prior.AimWordAlignedTests.rejects
    def test_entry_actual_call_and_zero_preservation(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimCacheCall.lean').exists(),'actual cache CALL proof missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v) :
    ∃ h<8, (∃ n≤5304, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (entered s h)) ∧
      (entered s h).pc=0x38d00 ∧
      (entered s h).core.regs 0=9 ∧ (entered s h).core.regs 2=1 ∧
      (entered s h).core.regs 5=0 ∧ (entered s h).core.regs 4=s.regs 4-36 ∧
      load32 (entered s h).core.memory (s.regs 4-36)=0x2e445 ∧
      ∀ j<11664, (entered s h).core.memory (v.block+24+BitVec.ofNat 32 j)=0 :=
  entry_execution s f table initial v heap frame aligned safe
''')
    def test_original_word_frame(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (a : Word) (readSafe : ReadSafe s v a) :
    load32 (entered s h).core.memory a=load32 s.memory a :=
  entry_frame s f table initial v heap frame h small safe a readSafe
''')
if __name__=='__main__': unittest.main()

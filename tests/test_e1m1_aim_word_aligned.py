"""All four-byte-aligned heads and residual word tails, exact execution."""
import sys, unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_word_fill as prior
ROOT=prior.ROOT
HEADER='''import Doom.Proofs.E1M1AimWordAligned
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWordFill E1M1AimWordAligned
'''
class AimWordAlignedTests(unittest.TestCase):
    lean=prior.AimWordFillTests.lean
    succeeds=prior.AimWordFillTests.succeeds
    rejects=prior.AimWordFillTests.rejects
    def test_head_from_initial_alignment(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimWordAligned.lean').exists(),'alignment head proof missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (count : s.regs 1=2916) (zero : s.regs 2=0)
    (aligned : readByte s.regs 0 &&& 3=0) :
    ∃ h<8, ∃ n≤46, ∃ t : X86WordFillRoutine.State,
      X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41917⟩ t ∧
      t.pc=0x41927 ∧ t.core=headCore s h ∧
      readByte t.core.regs 0 &&& 31=0 := head_execution s f count zero aligned
''')
    def test_grouped_remainder_execution(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge) (w : Nat)
    (low : 2909≤w) (high : w≤2916) (count : s.regs 1=BitVec.ofNat 32 w)
    (zero : s.regs 2=0) :
    ∃ n≤5110, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41927⟩
      ⟨doneCore (groupStart s w).core (4*(w/4)),g,0x41967⟩ :=
  grouped_execution s f w low high count zero
''')
    def test_all_residual_tails(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge) (w : Nat)
    (low : 2909≤w) (high : w≤2916) (saved : load32 s.memory (s.regs 4)=BitVec.ofNat 32 w)
    (zero : s.regs 2=0) :
    ∃ n≤13, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41967⟩
      ⟨tailCore s (w%4),g,0x41982⟩ := tail_execution s f w low high saved zero
''')
    def test_body_late_push_and_all_bytes(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (count : s.regs 1=2916) (zero : s.regs 2=0)
    (align : readByte s.regs 0 &&& 3=0) (safe : BodySafe s) :
    ∃ h<8, (∃ n≤5170, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41917⟩
      ⟨bodyCore s h,g,0x41982⟩) ∧
      ∀ j<11664, (bodyCore s h).memory (s.regs 0+BitVec.ofNat 32 j)=0 :=
  body_execution s f count zero align safe
''')
    def test_original_entry_complete_four_aligned(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (align : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v) :
    ∃ h<8, (∃ n≤5300, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (finished s h)) ∧
      (finished s h).pc=0x2e437 ∧
      ∀ j<11664, (finished s h).core.memory (v.block+24+BitVec.ofNat 32 j)=0 :=
  entry_execution s f table initial v heap frame align safe
''')
    def test_exact_registers_and_protected_words(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (h : Nat) (small : h<8) :
    (completed s h).core.regs=write (write (write s.regs 1 9) 2 0) 4 (s.regs 4+4) :=
  completed_registers s h small
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (before : E1M1AimSideMemset.EntrySafe s 0x2c11c) (output : OutputSafe s v 0x2c11c) :
    load32 (finished s h).core.memory 0x2c11c=648 :=
  entry_count_preserved s f table initial v heap frame h small safe before output
''')
    def test_cumulative_certificate_bytes_maps_and_strict_audit(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_word_aligned.py').exists(), 'aligned certificate missing')
        import verify_e1m1_aim_word_aligned as p, copy
        text=p.certificate(); output=self.succeeds(text); p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('entry_execution_checked','missing',1)]:
            with self.assertRaises(ValueError): p.audit(bad)
        for old,new in [('0xa8,0x1f,0x74,0x8','0xa8,0x1e,0x74,0x8'),
                        ('0x59,0x83,0xe1,0x3','0x59,0x83,0xe1,0x2')]:
            self.assertIn(old,text); self.rejects(text.replace(old,new,1))
        _,units,_=p.previous.previous.fill_data()
        for field in ['file_offset','code_offset']:
            bad=copy.deepcopy(units); bad['fill_words'][field]=hex(int(bad['fill_words'][field],16)+1)
            with self.assertRaises(ValueError): p.previous.previous.fill_data({'units':bad})
    def test_guards_cannot_be_erased(self):
        import verify_e1m1_aim_side_entry as p
        for name,guard in [
            ('entry_execution',"(aligned : (v.block+24).extractLsb' 0 8 &&& 3=0)"),
            ('entry_execution','(safe : Entry32Safe s v)'),
            ('body_memory','(safe : Doom.Proofs.E1M1AimWordAligned.BodySafe s)'),
            ('tail_execution','(saved : load32 s.memory (s.regs 4)=BitVec.ofNat 32 w)'),
            ('body_frame','(stack : Apart a (s.regs 4-4))'),
            ('heads_execution','(small : h<8)')]:
            decl,args=p.contract('E1M1AimWordAligned',name)
            decl=decl.replace('(f : Knowledge)','(f : X86WordFillRoutine.Knowledge)')
            text=HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.E1M1AimWordAligned.'+name+' '+args+'\n'
            self.succeeds(text); self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
if __name__=='__main__': unittest.main()

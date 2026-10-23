"""Opt-in honest flag projection and actual word-fill execution."""
import sys,unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_side_memset as prior
ROOT=prior.ROOT
class AimWordFillTests(unittest.TestCase):
    lean=prior.AimSideMemsetTests.lean
    succeeds=prior.AimSideMemsetTests.succeeds
    rejects=prior.AimSideMemsetTests.rejects
    def test_shift_projection_dec_and_unknown_consumers(self):
        self.assertTrue((ROOT/'Doom/Verification/X86WordFillRoutine.lean').exists(),'honest partial-flag interpreter missing')
        self.succeeds('''import Doom.Verification.X86WordFillRoutine
open Doom.Verification X86 X86Memory X86Control X86WordFillRoutine
example : X86WordFillRoutine.decode [0xc1,0xe9,0x02]=some (.shiftRightTwo 1,[]) := by decide +kernel
example : X86WordFillRoutine.decode [0x49]=some (.decrement 1,[]) := by decide +kernel
example (s : X86Memory.State) (f : Knowledge) (pc : Nat) :
    execute (.shiftRightTwo 1) ⟨s,f,pc⟩ = some ⟨put s 1 (s.regs 1 >>> 2),
      .zeroOnly ((s.regs 1 >>> 2)==0),pc⟩ := rfl
example (s : X86Memory.State) (f : Flags) (pc : Nat) :
    (execute (.decrement 1) ⟨s,.legacy (some f),pc⟩).map (fun t=>t.flags.carry)=some f.carry := rfl
example (s : X86Memory.State) (z : Bool) :
    execute (.base (.base (.base (.base (.control (.setle 0)))))) ⟨s,.zeroOnly z,20⟩=none := rfl
example (s : X86Memory.State) :
    execute (.base (.base (.base (.base (.control (.jumpZero true 7)))))) ⟨s,.zeroOnly true,20⟩=
      some ⟨s,.zeroOnly true,27⟩ := rfl
example (s : X86Memory.State) :
    execute (.base (.base (.base (.base (.control (.jumpZero true 7)))))) ⟨s,.legacy none,20⟩=none := rfl
''')
    def test_actual_pair_block_and_universal_zero_memory(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimWordFill.lean').exists(),'actual word filler proof missing')
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (zero : s.regs 2=0) (first : s.regs 1-1≠0) (second : s.regs 1-1-1≠0) :
    X86WordFillRoutine.Prefix program [] 14 ⟨s,f,0x41930⟩ (pairResult s) :=
  pair_execution s f zero first second
example (m : Memory) (a : Word) (n j : Nat) (h : j<4*n) :
    zeros m a n (a+BitVec.ofNat 32 j)=0 := zeros_byte m a n j h
''')
    def test_symbolic_pair_loop(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (k r : Nat) (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (zero : s.regs 2=0) (count : s.regs 1=BitVec.ofNat 32 (2*k+r))
    (positive : 0<r) (bound : 2*k+r<4294967296) :
    ∃ g, X86WordFillRoutine.Prefix program [] (14*k) ⟨s,f,0x41930⟩
      ⟨pairs s k,g,0x41930⟩ := pairs_execution k r s f zero count positive bound
example (s : X86Memory.State) (k : Nat) :
    (pairs s k).memory=zeros s.memory (s.regs 0) (8*k) := pairs_memory s k
''')
    def test_both_group_terminal_paths(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (zero : s.regs 2=0) (r : Nat) (small : r=1 ∨ r=2)
    (count : s.regs 1=BitVec.ofNat 32 r) :
    ∃ n≤21, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41930⟩
      ⟨doneCore s (4*(r+1)),g,0x41967⟩ := terminal_execution s f zero r small count
''')
    def test_full_group_loop(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (k r : Nat) (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (zero : s.regs 2=0) (count : s.regs 1=BitVec.ofNat 32 (2*k+r))
    (small : r=1 ∨ r=2) (bound : 2*k+r<4294967296) :
    ∃ n≤14*k+21, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41930⟩
      ⟨doneCore s (8*k+4*(r+1)),g,0x41967⟩ := groups_execution k r s f zero count small bound
''')
    def test_aligned32_body_zeroing_is_execution_not_cpu(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge)
    (count : s.regs 1=2916) (zero : s.regs 2=0)
    (aligned32 : readByte s.regs 0 &&& 31=0) :
    (∃ n≤5112, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41917⟩
      ⟨filled32 s,g,0x41967⟩) ∧
    (∀ j<11664, (filled32 s).memory (s.regs 0+BitVec.ofNat 32 j)=0) :=
  aligned32_body s f count zero aligned32
''')
    def test_actual_three_returns_and_preserved_memory(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (s : X86Memory.State) (f : X86WordFillRoutine.Knowledge) (base : Word)
    (saved : ReturnWords s base) :
    X86WordFillRoutine.Prefix program [] 11 ⟨s,f,0x41967⟩ (returned s base) :=
  returns_execution s f base saved
example (s : X86Memory.State) (base : Word) : (returned s base).core.memory=s.memory := rfl
''')
    def test_real_saved_words_and_completed_memset32(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open E1M1AimWordFill
example (s : X86Memory.State) (f : Option Flags)
    (zero : s.regs 2=0) (size : s.regs 3=11664) (index : s.regs 1=9)
    (ret : load32 s.memory (s.regs 4)=0x2e437)
    (aligned32 : readByte s.regs 0 &&& 31=0) (safe : Saved32Safe s) :
    (∃ n≤5140, X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed ⟨s,f,0x3fe70⟩)
      (completed32 s)) ∧ (completed32 s).pc=0x2e437 ∧
      (∀ j<11664, (completed32 s).core.memory (s.regs 0+BitVec.ofNat 32 j)=0) :=
  memset32_execution s f zero size index ret aligned32 safe
''')
    def test_original_entry32_zeroing_and_frame(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimWordFill
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned32 : (v.block+24).extractLsb' 0 8 &&& 31=0) (safe : Entry32Safe s v) :
    (∃ n≤5240, X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩)
      (finished32 s)) ∧ (finished32 s).pc=0x2e437 ∧
      (∀ j<11664, (finished32 s).core.memory (v.block+24+BitVec.ofNat 32 j)=0) :=
  entry32_execution s f table h v heap frame aligned32 safe
example (s : X86Memory.State) (a : Word)
    (stack : Apart a (s.regs 4-4))
    (safe : ∀ k<2916, Apart a (s.regs 0+BitVec.ofNat 32 (4*k))) :
    load32 (filled32 s).memory a=load32 s.memory a := filled32_frame s a stack safe
''')
    def test_required_guards_reject_mutations(self):
        import verify_e1m1_aim_side_entry as p
        header='''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimWordFill
'''
        for name,guard in [
          ('entry32_execution','(aligned32 : (v.block+24).extractLsb\' 0 8 &&& 31=0)'),
          ('entry32_execution','(safe : Doom.Proofs.E1M1AimWordFill.Entry32Safe s v)'),
          ('filled32_frame','(stack : Apart a (s.regs 4-4))'),
          ('pair_execution','(second : s.regs 1-1-1≠0)')]:
            decl,args=p.contract('E1M1AimWordFill',name)
            decl=decl.replace('(f : Knowledge)','(f : Doom.Verification.X86WordFillRoutine.Knowledge)')
            text=header+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.E1M1AimWordFill.'+name+' '+args+'\n'
            self.succeeds(text);self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
    def test_cumulative_certificate(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_word_fill.py').exists(),'word fill certificate missing')
        import verify_e1m1_aim_word_fill as p,copy
        text=p.certificate();output=self.succeeds(text);p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('entry32_execution_checked','missing',1)]:
            with self.assertRaises(ValueError):p.audit(bad)
        for old,new in [('0x51,0xc1,0xe9,0x2','0x51,0xc1,0xe9,0x3'),('0x4,0x49,0x75,0xf4','0x4,0x41,0x75,0xf4')]:
            self.assertIn(old,text);self.rejects(text.replace(old,new,1))
        _,units,_=p.previous.fill_data()
        for field in ['file_offset','code_offset']:
            bad=copy.deepcopy(units);bad['fill_words'][field]=hex(int(bad['fill_words'][field],16)+1)
            with self.assertRaises(ValueError):p.previous.fill_data({'units':bad})
    def test_count_and_caller_frames_survive_zeroing(self):
        self.succeeds('''import Doom.Proofs.E1M1AimWordFill
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimWordFill
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (before : E1M1AimSideMemset.EntrySafe s 0x2c11c) (output : OutputSafe s v 0x2c11c) :
    load32 (finished32 s).core.memory 0x2c11c=648 := entry32_count_preserved s f table h v heap frame before output
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (a : Word) (ha : a∈E1M1AimSidePublish.upperWords s)
    (before : E1M1AimSideMemset.EntrySafe s a) (output : OutputSafe s v a) :
    load32 (finished32 s).core.memory a=load32 (E1M1AimSideEntry.savedMemory s) a :=
  entry32_upper_preserved s f table h v heap frame a ha before output
''')
if __name__=='__main__':unittest.main()

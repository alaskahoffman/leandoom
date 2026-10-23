"""Frames from actual allocation and publication, not a reached memset image."""
import sys, unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
import test_e1m1_aim_side_entry as prior
ROOT = prior.ROOT
HEADER = '''import Doom.Proofs.E1M1AimSidePublish
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalGroupHeap (View)
open E1M1AimSideEntry (Initial savedMemory)
open E1M1AimSideAllocate (HeapInitial allocated)
open E1M1AimSidePublish
'''
class AimSidePublishTests(unittest.TestCase):
    lean = prior.AimSideEntryTests.lean
    succeeds = prior.AimSideEntryTests.succeeds
    rejects = prior.AimSideEntryTests.rejects
    def test_actual_allocation_preserves_count_index_and_saved_words(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSidePublish.lean').exists(), 'allocation frames missing')
        self.succeeds(HEADER + '''
example (s : X86Memory.State) (table : Word) (h : Initial s table)
    (v : View) (heap : HeapInitial s v) (frame : AllocationFrame s v) :
    load32 (allocated s).core.memory 0x2c11c=648 ∧
    (allocated s).core.regs 1=9 ∧
    (allocated s).core.regs 5=s.regs 5 ∧
    (allocated s).core.regs 6=s.regs 6 ∧
    (allocated s).core.regs 7=s.regs 7 := allocation_inputs s table h v heap frame
example (s : X86Memory.State) (v : View) (heap : HeapInitial s v)
    (frame : AllocationFrame s v) (a : Word) (ha : a∈upperWords s) :
    load32 (allocated s).core.memory a=load32 (savedMemory s) a :=
  allocation_upper s v heap frame a ha
example (s : X86Memory.State) (v : View) (heap : HeapInitial s v)
    (a : Word) (safe : InitialSafe s v a) :
    load32 (allocated s).core.memory a=load32 s.memory a :=
  allocation_frame s v heap a safe
''')
    def test_connected_publication_to_real_memset_call(self):
        self.succeeds(HEADER + '''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) (v : View) (heap : HeapInitial s v) (frame : AllocationFrame s v) :
    (∃ n≤100, X86StartupRoutine.Prefix E1M1AimSideAllocate.program [] n
      ⟨s,f,0x2e3e0⟩ (published s)) ∧ (published s).pc=0x3fe70 ∧
      (published s).core.regs 0=v.block+24 ∧ (published s).core.regs 1=9 ∧
      (published s).core.regs 2=0 ∧ (published s).core.regs 3=11664 ∧
      (published s).core.regs 4=s.regs 4-36 ∧
      load32 (published s).core.memory ((published s).core.regs 4)=0x2e437 :=
  execution s f table h v heap frame
''')
    def test_cumulative_certificate_and_negative_mutations(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_publish.py').exists(), 'publication verifier missing')
        import verify_e1m1_aim_side_publish as p
        text=p.certificate(); output=self.succeeds(text); p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('published_count_checked','missing',1)]:
            with self.assertRaises(ValueError): p.audit(bad)
        old='0x89,0xc3,0xa3,0x18,0xc1'
        self.assertIn(old,text); self.rejects(text.replace(old,'0x89,0xc3,0xa3,0x1c,0xc1',1))
    def test_independent_publication_oracle(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_publish.py').exists(), 'publication CPU oracle missing')
        import subprocess,os,json
        r=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c',
            'import verify_e1m1_aim_side_publish as p,json; print(json.dumps(p.cross_check()))'],
            cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=90)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        d=json.loads(r.stdout); self.assertEqual(d['cases'],64)
        self.assertTrue(d['ordered_writes']); self.assertTrue(d['all_registers'])
        self.assertTrue(d['publication']); self.assertTrue(d['upper_saved_words'])
    def test_allocation_and_publication_guards_required(self):
        import verify_e1m1_aim_side_entry as p
        for name,guard in [('execution','(frame : Doom.Proofs.E1M1AimSidePublish.AllocationFrame s v)'),
                           ('published_base','(safe : Apart 0x2c118 (s.regs 4-36))')]:
            decl,args=p.contract('E1M1AimSidePublish',name)
            text=HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.E1M1AimSidePublish.'+name+' '+args+'\n'
            self.succeeds(text); self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))

if __name__ == '__main__': unittest.main()


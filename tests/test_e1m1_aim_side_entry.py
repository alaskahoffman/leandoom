"""Actual loader entry, including W_LumpLength, not allocation success."""
import sys, unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_side_cleanup as prior
ROOT=prior.ROOT
HEADER='import Doom.Proofs.E1M1AimSideEntry\nopen Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary E1M1AimSideEntry\n'
class AimSideEntryTests(unittest.TestCase):
    lean=prior.AimSideCleanupTests.lean
    succeeds=prior.AimSideCleanupTests.succeeds
    rejects=prior.AimSideCleanupTests.rejects
    def test_entry_to_actual_allocation_request(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideEntry.lean').exists(),'actual entry/length theorem missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) :
    X86StartupRoutine.Prefix program [] 30 ⟨s,f,0x2e3e0⟩ (request s) :=
  execution s f table h
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) :
    (request s).pc=0x39690 ∧ (request s).core.regs 0=11664 ∧
    (request s).core.regs 2=50 ∧ (request s).core.regs 3=0 ∧
    load32 (request s).core.memory ((request s).core.regs 4)=0x2e415 ∧
    load32 (request s).core.memory 0x2c11c=648 := request_observations s table h
''')
    def test_unsigned_divide_faults_and_remainder(self):
        self.assertTrue((ROOT/'Doom/Verification/X86StartupRoutine.lean').exists(),'opt-in unsigned DIV missing')
        self.succeeds('''import Doom.Verification.X86StartupRoutine
open Doom.Verification X86 X86Memory X86Control X86StartupRoutine
example : X86StartupRoutine.decode [0xf7,0xf3]=some (.unsignedDivide 3,[]) := by decide +kernel
example (s : X86Control.State) (zero : s.core.regs 3=0) :
    X86StartupRoutine.execute (.unsignedDivide 3) s=none := by simp [X86StartupRoutine.execute,zero]
example (s : X86Control.State) (hi : s.core.regs 2=1)
    (lo : s.core.regs 0=0) (d : s.core.regs 3=1) :
    X86StartupRoutine.execute (.unsignedDivide 3) s=none := by simp [X86StartupRoutine.execute,hi,lo,d]
example (s : X86Control.State) (hi : s.core.regs 2=0)
    (lo : s.core.regs 0=19441) (d : s.core.regs 3=30) :
    X86StartupRoutine.execute (.unsignedDivide 3) s=
      some {s with core:=put (put s.core 0 648) 2 1,flags:=none} := by
  simp [X86StartupRoutine.execute,hi,lo,d]
''')
    def test_entry_through_real_selected_allocation(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideAllocate.lean').exists(),'connected allocation missing')
        self.succeeds('import Doom.Proofs.E1M1AimSideAllocate\n'+HEADER+'''
open E1M1AimSideAllocate
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : Initial s table) (v : OriginalGroupHeap.View) (heap : HeapInitial s v) :
    (∃ n≤90, X86StartupRoutine.Prefix E1M1AimSideAllocate.program [] n
      ⟨s,f,0x2e3e0⟩ (allocated s)) ∧ (allocated s).pc=0x2e415 ∧
      (allocated s).core.regs 0=v.block+24 ∧ (allocated s).core.regs 4=s.regs 4-32 :=
  E1M1AimSideAllocate.execution s f table h v heap
''')

    def test_cumulative_bytes_and_strict_audit(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_entry.py').exists(),'entry certificate missing')
        import verify_e1m1_aim_side_entry as proof
        text=proof.certificate();output=self.succeeds(text);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('execution_checked','missing',1)]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for old,new in [('0xf7,0xf3,0xa3','0xf7,0xfb,0xa3'),('0x3b,0x5,0xa0,0x4f','0x3b,0x5,0xa4,0x4f'),
                        ('def lumpLength : Nat := 19440','def lumpLength : Nat := 19441')]:
            self.assertIn(old,text);self.rejects(text.replace(old,new,1))
        import copy
        units=proof.entry_data()[1]
        for field,value in [('file_offset','0x703f5'),('code_offset','0x2e3e1')]:
            bad=copy.deepcopy(units);bad['entry'][field]=value
            with self.assertRaises(ValueError):proof.entry_data({'units':bad})
        bad=copy.deepcopy(units);bad['length']['relocations'][0]['object']=1
        with self.assertRaises(ValueError):proof.entry_data({'units':bad})
    def test_independent_connected_entry_allocation(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_entry.py').exists(),'independent entry/allocation oracle missing')
        import subprocess,os,json
        r=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c',
          'import verify_e1m1_aim_side_entry as p,json; print(json.dumps(p.cross_check()))'],
          cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=90)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        data=json.loads(r.stdout);self.assertEqual(data['cases'],64)
        self.assertTrue(data['ordered_writes']);self.assertTrue(data['all_registers'])
    def test_initial_guards_required(self):
        import verify_e1m1_aim_side_entry as p
        for module,name,guard in [
            ('E1M1AimSideEntry','execution','(h : Doom.Proofs.E1M1AimSideEntry.Initial s table)'),
            ('E1M1AimSideAllocate','execution','(heap : Doom.Proofs.E1M1AimSideAllocate.HeapInitial s v)')]:
            decl,args=p.contract(module,name)
            text='import Doom.Proofs.E1M1AimSideAllocate\n'+p.HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds(text);self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
if __name__=='__main__':unittest.main()

"""Real nested memset prefix; does not assert the open fill/return theorem."""
import sys,unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_side_publish as prior
ROOT=prior.ROOT
HEADER='''import Doom.Proofs.E1M1AimSideMemset
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimSideMemset
'''
class AimSideMemsetTests(unittest.TestCase):
    lean=prior.AimSidePublishTests.lean
    succeeds=prior.AimSidePublishTests.succeeds
    rejects=prior.AimSidePublishTests.rejects
    def test_actual_two_nested_calls_not_assumed_helper_success(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideMemset.lean').exists(),'nested memset execution missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags)
    (zero : s.regs 2=0) (size : s.regs 3=11664)
    (aligned : readByte s.regs 0 &&& 3=0) :
    X86FillRoutine.Prefix program [] 17 ⟨s,f,0x3fe70⟩ (wordsCalled s) :=
  nested_execution s f zero size aligned
example (s : X86Memory.State) (a : Word) (safe : SafeWord s a) :
    load32 (wordsCalled s).core.memory a=load32 s.memory a :=
  nested_frame s a safe
''')
    def test_opt_in_decoder_and_partial_byte_semantics(self):
        self.assertTrue((ROOT/'Doom/Verification/X86FillRoutine.lean').exists(),'opt-in fill semantics missing')
        self.succeeds('''import Doom.Verification.X86FillRoutine
open Doom.Verification X86 X86Memory X86Control
example : X86FillRoutine.decode [0x8a,0xf2]=some (.base (.base (.base (.moveByte 6 2))),[]) := by decide +kernel
example : X86FillRoutine.decode [0x0b,0xc9]=some (.orRegisters 1 1,[]) := by decide +kernel
example : X86FillRoutine.decode [0x38,0x10]=some (.compareMemoryByte ⟨some 0,none,0,0⟩ 2,[]) := by decide +kernel
example : X86FillRoutine.decode [0xa8,0x03]=some (.base (.base (.base (.testByteImmediate 0 3))),[]) := by decide +kernel
example (s : X86Control.State) (h : s.core.regs 2=0x12345678) :
    (X86FillRoutine.execute (.base (.base (.base (.moveByte 6 2)))) s).map (fun t=>t.core.regs 2)=some 0x12347878 := by
  simp [X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
    putByte,readByte,byteReg,put,write,h,show (6:Reg).val=6 from rfl,show Fin.ofNat 8 2=(2:Reg) from rfl]
''')
    def test_connected_initial_entry_to_word_filler(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) :
    (∃ n≤117, X86FillRoutine.Prefix program [] n ⟨s,f,0x2e3e0⟩ (nested s)) ∧
    (nested s).pc=0x41917 ∧ (nested s).core.regs 0=v.block+24 ∧
    (nested s).core.regs 1=2916 ∧ (nested s).core.regs 2=0 ∧
    (nested s).core.regs 4=s.regs 4-56 := execution s f table h v heap frame aligned
''')
    def test_count_base_upper_and_arbitrary_frames_through_nested_calls(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (a : Word)
    (safe : EntrySafe s a) :
    load32 (nested s).core.memory a=load32 (E1M1AimSideAllocate.allocated s).core.memory a :=
  allocation_frame s f table h v heap a safe
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (frame : E1M1AimSidePublish.AllocationFrame s v) (safe : EntrySafe s 0x2c11c) :
    load32 (nested s).core.memory 0x2c11c=648 := count_preserved s f table h v heap frame safe
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (safe : OriginalGroupHeap.Separated 0x2c118
      [s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56]) :
    load32 (nested s).core.memory 0x2c118=v.block+24 := base_preserved s f table h v heap safe
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v)
    (frame : E1M1AimSidePublish.AllocationFrame s v) (a : Word)
    (ha : a∈E1M1AimSidePublish.upperWords s) (safe : EntrySafe s a) :
    load32 (nested s).core.memory a=load32 (E1M1AimSideEntry.savedMemory s) a :=
  upper_preserved s f table h v heap frame a ha safe
''')
    def test_cumulative_certificate_and_negative_mutations(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_memset.py').exists(),'nested certificate missing')
        import verify_e1m1_aim_side_memset as p,copy
        text=p.certificate();output=self.succeeds(text);p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('nested_execution_checked','missing',1)]:
            with self.assertRaises(ValueError):p.audit(bad)
        for old,new in [('0x50,0x51,0x8a,0xf2','0x50,0x51,0x8a,0xd2'),('0xa8,0x3,0x74','0xa8,0x7,0x74')]:
            self.assertIn(old,text);self.rejects(text.replace(old,new,1))
        _,units,_=p.fill_data()
        for field in ['file_offset','code_offset']:
            bad=copy.deepcopy(units);bad['memset'][field]=hex(int(bad['memset'][field],16)+1)
            with self.assertRaises(ValueError):p.fill_data({'units':bad})
        bad=copy.deepcopy(units);bad['fill']['relocations']=[{'offset':0,'object':1,'target':'0x0'}]
        with self.assertRaises(ValueError):p.fill_data({'units':bad})
    def test_full_memset_cpu_is_separate_empirical_evidence(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_side_memset.py').exists(),'memset CPU oracle missing')
        import subprocess,os,json
        r=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c',
            'import verify_e1m1_aim_side_memset as p,json; print(json.dumps(p.cross_check()))'],
            cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=180)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        d=json.loads(r.stdout);self.assertEqual(d['cases'],512)
        self.assertTrue(d['all_registers']);self.assertTrue(d['full_mapped_data'])
        self.assertTrue(d['zeroed_11664_bytes']);self.assertTrue(d['ordered_writes'])
        self.assertFalse(d['universal_memset_theorem'])
    def test_alignment_is_a_real_proof_guard(self):
        import verify_e1m1_aim_side_entry as p
        decl,args=p.contract('E1M1AimSideMemset','nested_execution')
        text=HEADER+decl.replace('theorem nested_execution','example',1)+' := by\n  exact Doom.Proofs.E1M1AimSideMemset.nested_execution '+args+'\n'
        self.succeeds(text);guard='(aligned : readByte s.regs 0 &&& 3=0)';self.assertIn(guard,text)
        self.rejects(text.replace(guard,'(aligned : True)'))
        for name,guard in [('allocation_frame','(safe : Doom.Proofs.E1M1AimSideMemset.EntrySafe s a)'),
                           ('nested_frame','(safe : Doom.Proofs.E1M1AimSideMemset.SafeWord s a)')]:
            decl,args=p.contract('E1M1AimSideMemset',name)
            text=HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.E1M1AimSideMemset.'+name+' '+args+'\n'
            self.succeeds(text);self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
if __name__=='__main__':unittest.main()

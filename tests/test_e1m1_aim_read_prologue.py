"""Actual read prologue and disk-icon gate, never a callee-success oracle."""
import sys, unittest
sys.setrecursionlimit(max(10000,sys.getrecursionlimit()))
import test_e1m1_aim_cache_heap as prior
ROOT=prior.ROOT
HEADER='''import Doom.Proofs.E1M1AimReadPrologue
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimReadPrologue
'''
class AimReadPrologueTests(unittest.TestCase):
    lean=prior.AimCacheHeapTests.lean
    succeeds=prior.AimCacheHeapTests.succeeds
    rejects=prior.AimCacheHeapTests.rejects
    def test_read_prologue_actual_icon_call(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimReadPrologue.lean').exists(),'actual W_ReadLump prologue missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (table : Word)
    (index : s.regs 0=9) (count : load32 s.memory 0x74fa0=1264)
    (pointer : load32 s.memory 0x74fa4=table)
    (countSafe : Safe s 0x74fa0) (pointerSafe : Safe s 0x74fa4) :
    X86WordFillRoutine.Prefix program [] 15 (X86WordFillRoutine.embed ⟨s,f,0x38bf0⟩) (iconCalled s table) := by
  exact local_execution s f table index count pointer countSafe pointerSafe
''')
    def test_original_entry_connected_with_original_address_frames(self):
        self.succeeds(HEADER+'''#check E1M1AimReadPrologue.entry_execution
#check E1M1AimReadPrologue.entry_frame
#check E1M1AimReadPrologue.output_preserved
''')
    def test_actual_disk_gate_and_conditional_return(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimDiskRead.lean').exists(),'disk-icon implementation proof missing')
        self.succeeds('''import Doom.Proofs.E1M1AimDiskRead
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimDiskRead
example (s : X86Memory.State) (f : Option Flags) (value : Word)
    (flag : load32 s.memory 0x29134=value) (safe : Safe s 0x29134) :
    X86WordFillRoutine.Prefix program [] 5 (X86WordFillRoutine.embed ⟨s,f,0x1adb0⟩) (gate s value) := by
  exact gate_execution s f value flag safe
example (s : X86Memory.State) :
    X86WordFillRoutine.Prefix program [] 4 (gate s 0) (returned s) := by
  exact disabled_return s
''')
    def test_original_icon_value_selects_real_path(self):
        self.succeeds('''import Doom.Proofs.E1M1AimDiskRead
#check Doom.Proofs.E1M1AimDiskRead.entry_execution
#check Doom.Proofs.E1M1AimDiskRead.entry_frame
#check Doom.Proofs.E1M1AimDiskRead.result_memory
''')
    def test_real_file_requests_not_successful_wrappers(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimReadRequest.lean').exists(),'actual read-file request proof missing')
        self.succeeds('''import Doom.Proofs.E1M1AimReadRequest
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open E1M1AimReadRequest
example (s : X86Memory.State) (f : Option Flags) (handle offset : Word)
    (cell : load32 s.memory (s.regs 1+8)=handle) (opened : handle≠ -1)
    (position : load32 s.memory (s.regs 1+12)=offset) :
    X86WordFillRoutine.Prefix program [] 8 (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (seekCalled s handle offset) := by
  exact seek_execution s f handle offset cell opened position
example (s : X86Memory.State) (f : Option Flags) (name : Word)
    (cell : load32 s.memory (s.regs 1+8)= -1) (filename : load32 s.memory 0x74f9c=name)
    (safe : Apart 0x74f9c (s.regs 4-4)) :
    X86WordFillRoutine.Prefix program [] 7 (X86WordFillRoutine.embed ⟨s,f,0x38c2b⟩) (openCalled s name) := by
  exact open_execution s f name cell filename safe
''')
    def test_original_file_choice_and_payload_frames(self):
        self.succeeds('''import Doom.Proofs.E1M1AimReadRequest
#check Doom.Proofs.E1M1AimReadRequest.entry_execution
#check Doom.Proofs.E1M1AimReadRequest.request_memory
#check Doom.Proofs.E1M1AimDiskRead.byte_frame
''')
    def test_authenticated_certificate_and_mutations(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_read_prologue.py').exists(),'read cumulative certificate missing')
        import verify_e1m1_aim_read_prologue as p, copy
        text=p.certificate(); output=self.succeeds(text); p.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('read_checked','missing',1)]:
            with self.assertRaises(ValueError): p.audit(bad)
        for old,new in [('0x53,0x51,0x56,0x57,0x55,0x89,0xc7','0x53,0x51,0x56,0x57,0x55,0x89,0xc6'),
                        ('0x53,0x51,0x52,0x83,0x3d,0x34,0x91','0x53,0x51,0x52,0x83,0x3d,0x35,0x91'),
                        ('0xe8,0x50,0x7c,0x0,0x0','0xe8,0x51,0x7c,0x0,0x0')]:
            self.assertIn(old,text); self.rejects(text.replace(old,new,1))
        _,units,_=p.read_data()
        for field in ['file_offset','code_offset']:
            bad=copy.deepcopy(units);bad['read'][field]=hex(int(bad['read'][field],16)+1)
            with self.assertRaises(ValueError):p.read_data({'units':bad})
        bad=copy.deepcopy(units);bad['beginRead']['relocations'][0]['target']='0x29135'
        with self.assertRaises(ValueError):p.read_data({'units':bad})
    def test_original_guards_and_disabled_condition_are_required(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_read_prologue.py').exists(),'read cumulative certificate missing')
        import verify_e1m1_aim_read_prologue as p
        for module,name,guard in [('E1M1AimReadPrologue','entry_execution','bodySafe'),
                                 ('E1M1AimReadPrologue','output_preserved','stack'),
                                 ('E1M1AimDiskRead','entry_execution','iconSafe'),
                                 ('E1M1AimReadRequest','entry_execution','disabled'),
                                 ('E1M1AimReadRequest','entry_execution','fileSafe'),
                                 ('E1M1AimReadRequest','open_execution','safe')]:
            decl,args=p.contract(module,name)
            prefix=p.HEADER+decl.replace('theorem '+name,'example',1)+' := by\n  exact Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds('import Doom.Proofs.E1M1AimReadRequest\n'+prefix)
            start=prefix.index('('+guard+' :');depth=1;end=start+1
            while depth:
                depth+=(prefix[end]=='(')-(prefix[end]==')');end+=1
            self.rejects('import Doom.Proofs.E1M1AimReadRequest\n'+prefix[:start]+'('+guard+' : True)'+prefix[end:])
    def test_independent_original_entry_cpu(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_read_prologue.py').exists(),'read CPU verifier missing')
        import verify_e1m1_aim_read_prologue as p
        self.assertTrue(hasattr(p,'cross_check'),'independent continuous CPU path missing')
        import subprocess
        run=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c',
            'import verify_e1m1_aim_read_prologue as p; r=p.cross_check(); assert r["cases"]>0; print(r["modes"])'],
            cwd=ROOT,env={**__import__('os').environ,'PYTHONPATH':str(ROOT/'scripts')},capture_output=True,text=True,timeout=300)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
    def test_new_stack_guards_and_hardware_fail_closed(self):
        self.succeeds(HEADER+'''
example : OriginalGroupHeap.Separated (0x680100-76)
    [0x680100-60,0x680100-64,0x680100-68,0x680100-72] ∧
    ¬OriginalGroupHeap.Separated (0x680100-76)
    [0x680100-60,0x680100-64,0x680100-68,0x680100-72,0x680100-76] := by
  simp [OriginalGroupHeap.Separated]
  unfold Apart
  decide +kernel
example : program 0x1adc7=none := by decide +kernel
example : program 0x408d9=none := by decide +kernel
''')
if __name__=='__main__': unittest.main()

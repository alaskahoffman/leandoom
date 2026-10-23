"""Complete bounded original comparator, including real table-call return."""
import sys,unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_texture_iteration as prior
HEADER='import Doom.Proofs.OriginalTextureComparator\n'+prior.prior.proof.HEADER+'\nopen OriginalTextureIteration OriginalTextureComparator\n'
class AimTextureComparatorTests(unittest.TestCase):
    lean=prior.AimTextureIterationTests.lean
    succeeds=prior.AimTextureIterationTests.succeeds
    rejects=prior.AimTextureIterationTests.rejects
    def test_header_gates(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (h : s.regs 3=0) :
    X86ByteRoutine.Prefix program [] 4 ⟨s,f,0x4198d⟩ (zeroExit s) := gate_zero s f h
example (s : X86Memory.State) (f : Option Flags) (h : s.regs 3≠0) :
    X86ByteRoutine.Prefix program [] 2 ⟨s,f,0x4198d⟩
      ⟨s,some (logical32 (s.regs 3)),0x41995⟩ := gate_nonzero s f h
''')
    def test_bounded_repetition(self):
        self.succeeds(HEADER+'''
example (n : Nat) (s : X86Memory.State) (f : Option Flags) (h : (s.regs 3).toNat=n) :
    ∃ k≤22*n+4, X86ByteRoutine.Prefix program [] k ⟨s,f,0x4198d⟩ (loop n s) := loop_execution n s f h
example (n : Nat) (s : X86Memory.State) : (loop n s).pc=0x419cc := loop_exit n s
''')
    def test_complete_return_and_restoration(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤22*(s.regs 3).toNat+7, X86ByteRoutine.Prefix program [] k ⟨s,f,0x4198c⟩ (complete s) := complete_execution s f
example (s : X86Memory.State) (safe : Apart (s.regs 4) (s.regs 4-4)) :
    (complete s).core.regs 1=s.regs 1 ∧ (complete s).core.regs 4=s.regs 4+4 ∧
      (complete s).pc=(load32 s.memory (s.regs 4)).toNat := complete_restoration s safe
example (s : X86Memory.State)
    (safe : Apart ((OriginalTextureTable.comparison s).core.regs 4)
      ((OriginalTextureTable.comparison s).core.regs 4-4)) :
    ∃ k≤183, X86ByteRoutine.Prefix program [] k (OriginalTextureTable.comparison s)
      (complete (OriginalTextureTable.comparison s).core) ∧
      (complete (OriginalTextureTable.comparison s).core).pc=0x34722 := table_return s safe
''')
    def test_exact_result_semantics(self):
        self.succeeds(HEADER+'''
example (n : Nat) (s : X86Memory.State) :
    (loop n s).core.regs 0=compareBytes n s.memory (s.regs 0) (s.regs 2) := loop_result n s
example (s : X86Memory.State) :
    (complete s).core.regs 0=compareBytes (s.regs 3).toNat
      (prepared s).memory (s.regs 0) (s.regs 2) := complete_result s
''')
    def test_table_call_composition(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags)
    (safe : Apart ((OriginalTextureTable.comparison s).core.regs 4)
      ((OriginalTextureTable.comparison s).core.regs 4-4)) :
    ∃ k≤189, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x3470c⟩
      (complete (OriginalTextureTable.comparison s).core) ∧
      (complete (OriginalTextureTable.comparison s).core).pc=0x34722 := table_call_return s f safe
''')
    def test_cumulative_certificate_and_mutations(self):
        self.assertTrue((prior.prior.proof.ROOT/'scripts/verify_e1m1_aim_texture_comparator.py').is_file(), 'complete comparator certificate generator missing')
        import verify_e1m1_aim_texture_comparator as proof
        import re,copy,json
        data,_=proof.previous.previous.pinned_data();_,_,raw=proof.previous.previous.extracted()
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),
                    output.replace('loop_execution_checked','missing'),
                    output.replace('table_call_return_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.rejects(source.replace('0x51,0x85,0xdb','0x52,0x85,0xdb'))
        self.rejects(source.replace('0x74,0xc,0x31','0x75,0xc,0x31'))
        self.assertEqual([n for n,_ in proof.CONTRACTS],re.findall(r'^theorem (\w+) ',(proof.ROOT/'Doom/Proofs/OriginalTextureComparator.lean').read_text(),re.M))
        e=proof.previous.previous.extraction_support.extraction
        spec=json.loads((proof.ROOT/'tests/reference/original-texture-iteration.json').read_text())
        profile=json.loads((proof.ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((proof.ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(proof.ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for unit,field,value in [('entry','file_offset','0x839a1'),('suffix','hex','750c'+spec['units']['suffix']['hex'][4:])]:
            bad=copy.deepcopy(spec);bad['units'][unit][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
    def test_independent_complete_calls(self):
        import verify_e1m1_aim_texture_comparator as proof
        self.assertTrue(callable(getattr(proof,'cross_check',None)), 'complete comparator independent check missing')
        import subprocess,json,os
        result=subprocess.run([str(proof.ROOT/'.tools/x86-check/bin/python'),'-c',
            'import json; import verify_e1m1_aim_texture_comparator as p; print(json.dumps(p.cross_check(p.previous.iteration_data()[0])))'],
            cwd=proof.ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=180)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        report=json.loads(result.stdout)
        self.assertEqual(report['bounds'],list(range(9)))
        self.assertEqual(report['bound8_mismatch_positions'],list(range(8)))
        self.assertEqual(report['bound8_nul_positions'],list(range(8)))
        self.assertTrue(report['all_registers_memory_ordered_writes'])
        self.assertGreater(report['joined_table_calls'],0)
        self.assertGreater(report['wrapping_stack_cases'],0)
        self.assertGreater(report['wrapping_name_cases'],0)
        self.assertGreater(report['large_count_early_exits'],0)
    def test_eighth_byte_limits_high_bytes_and_aliasing(self):
        self.succeeds(HEADER+'''
def fixture (n : Word) (v : BitVec 8) (nul : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x100 else if r=2 then 0x200 else if r=3 then n else if r=4 then 0x800 else 0x12345678,
   fun p => if nul && (p=0x104 || p=0x204) then 0
     else if p=0x207 then v else if p=0x208 then 255
     else if 0x100≤p.toNat && p.toNat<0x109 then 65 else 97⟩
-- These reduce the memory-byte specification, never a long machine run.
example : (complete (fixture 8 97 false)).core.regs 0=0 := by
  rw [complete_result]; decide +kernel
example : (complete (fixture 8 255 false)).core.regs 0=0xffffff62 := by
  rw [complete_result]; decide +kernel
example : (complete (fixture 7 255 false)).core.regs 0=0 := by
  rw [complete_result]; decide +kernel
example : (complete (fixture 8 255 true)).core.regs 0=0 := by
  rw [complete_result]; decide +kernel
example : (complete (fixture 0 255 false)).core.regs 0=0 := by
  rw [complete_result]; decide +kernel
-- Pushed ECX overwrites a name: the pre-PUSH comparison would be equal,
-- but the actual comparator sees a zero left byte and returns -97.
def alias : X86Memory.State :=
  ⟨fun r => if r=0 then 0x7fc else if r=2 then 0x200 else if r=3 then 8 else if r=4 then 0x800 else 0,
    fun _ => 97⟩
example : compareBytes 8 alias.memory (alias.regs 0) (alias.regs 2)=0 := by decide +kernel
example : (complete alias).core.regs 0=0xffffff9f := by
  rw [complete_result]; decide +kernel
example (s : X86Memory.State) :
    (complete s).core.memory=(prepared s).memory := (complete_frame s).1
example (s : X86Memory.State) :
    (complete s).core.regs 7=s.regs 7 := (complete_frame s).2 7 (by decide) (by decide) (by decide) (by decide) (by decide)
''')
    def test_counter_and_branch_guards_are_required(self):
        import verify_e1m1_aim_texture_comparator as proof
        for name,args,old in [('loop_execution','n s f h','(h : (s.regs 3).toNat=n)'),
                               ('gate_nonzero','s f h','(h : s.regs 3≠0)'),
                               ('gate_zero','s f h','(h : s.regs 3=0)')]:
            decl=proof.declaration(name).replace('theorem '+name,'example',1)
            source=HEADER+decl+' := Doom.Proofs.OriginalTextureComparator.'+name+' '+args+'\n'
            self.succeeds(source)
            self.assertIn(old,source)
            self.rejects(source.replace(old,'(h : True)'))
if __name__=='__main__':unittest.main()

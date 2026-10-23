"""Complete original comparator iteration; no assumed helper execution."""
import unittest,sys
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_texture_fold as prior
HEADER='import Doom.Proofs.OriginalTextureIteration\n'+prior.proof.HEADER+'\nopen OriginalTextureIteration\n'
class AimTextureIterationTests(unittest.TestCase):
    lean=prior.AimTextureFoldTests.lean
    succeeds=prior.AimTextureFoldTests.succeeds
    rejects=prior.AimTextureFoldTests.rejects
    def test_original_loads(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.run program [0x41999] 2 ⟨s,f,0x41995⟩=some ⟨loaded s,f,0x41999⟩ := loads_execution s f
''')
    def test_complete_iteration(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤20, X86ByteRoutine.Prefix program [] n ⟨s,f,0x41995⟩ (iteration s) := iteration_execution s f
example (s : X86Memory.State) : (iteration s).core.memory=s.memory := iteration_memory s
''')
    def test_iteration_values_and_real_return(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) :
    readByte (foldedPair s).regs 1=OriginalTextureFold.lower (s.memory (s.regs 0)) ∧
    readByte (foldedPair s).regs 5=OriginalTextureFold.lower (s.memory (s.regs 2)) := loaded_fold_values s
example (s : X86Memory.State) :
    (mismatch s).regs 0=(readByte s.regs 1).zeroExtend 32-(readByte s.regs 5).zeroExtend 32 := mismatch_value s
example (s : X86Memory.State) (f : Option Flags)
    (done : (iteration s).pc=0x419cc) :
    ∃ n≤22, X86ByteRoutine.Prefix program [] n ⟨s,f,0x41995⟩ (restored (iteration s).core (iteration s).flags) := iteration_return s f done
''')
    def test_entry_and_caller_restoration(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (nonzero : s.regs 3≠0) :
    X86ByteRoutine.run program [0x41995] 3 ⟨s,f,0x4198c⟩=some ⟨prepared s,some (logical32 (s.regs 3)),0x41995⟩ := entry_execution s f nonzero
example (s : X86Memory.State) (f : Option Flags) (nonzero : s.regs 3≠0)
    (done : (iteration (prepared s)).pc=0x419cc) :
    ∃ n≤25, X86ByteRoutine.Prefix program [] n ⟨s,f,0x4198c⟩
      (restored (iteration (prepared s)).core (iteration (prepared s)).flags) := first_iteration_return s f nonzero done
#check table_first_return
''')
    def test_certificate_and_negative_mutations(self):
        import verify_e1m1_aim_texture_iteration as proof
        import copy,json,re
        data,_=proof.previous.pinned_data();_,_,raw=proof.previous.extracted()
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('iteration_execution_checked','missing'),output.replace('X86ByteRoutine.Prefix.trans','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.rejects(source.replace('0x51,0x85,0xdb','0x52,0x85,0xdb'))
        self.rejects(source.replace('0x74,0xc,0x31','0x75,0xc,0x31'))
        self.assertEqual([n for n,_ in proof.CONTRACTS],re.findall(r'^theorem (\w+) ',(proof.ROOT/'Doom/Proofs/OriginalTextureIteration.lean').read_text(),re.M))
        e=proof.previous.extraction_support.extraction
        spec=json.loads((proof.ROOT/'tests/reference/original-texture-iteration.json').read_text())
        profile=json.loads((proof.ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((proof.ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(proof.ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for unit,field,value in [('entry','file_offset','0x839a1'),('suffix','hex','750c'+spec['units']['suffix']['hex'][4:])]:
            bad=copy.deepcopy(spec);bad['units'][unit][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
    def test_outcomes_high_bytes_wraparound_and_aliasing(self):
        self.succeeds(HEADER+'''
def fixture (a b : BitVec 8) (count : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0xffffffff else if r=2 then 0x200 else if r=3 then count else if r=4 then 3 else 0x12340000,
    fun p => if p=0xffffffff then a else if p=0x200 then b else 0⟩
example : (iteration (fixture 0x80 1 8)).pc=0x419cc ∧
    (iteration (fixture 0x80 1 8)).core.regs 0=127 ∧
    (iteration (fixture 1 0xff 8)).core.regs 0=0xffffff02 := by decide +kernel
example : (iteration (fixture 65 97 0)).pc=0x4198d ∧
    (iteration (fixture 65 97 0)).core.regs 0=0 ∧
    (iteration (fixture 65 97 0)).core.regs 2=0x201 ∧
    (iteration (fixture 65 97 0)).core.regs 3=0xffffffff := by decide +kernel
example : (iteration (fixture 0 0 8)).pc=0x419cc ∧
    (iteration (fixture 0 0 8)).core.regs 0=0 ∧
    (iteration (fixture 0 0 8)).core.regs 3=8 := by decide +kernel
-- ESP=3 pushes ECX at 0xffffffff, replacing the first name byte before loads.
example : (loaded (prepared (fixture 65 97 8))).memory 0xffffffff=0 ∧
    readByte (loaded (prepared (fixture 65 97 8))).regs 1=0 := by decide +kernel
example (s : X86Memory.State) : (iteration s).core.regs 4=s.regs 4 := iteration_stack s
''')
    def test_return_and_entry_guards_cannot_be_dropped(self):
        import verify_e1m1_aim_texture_iteration as proof
        decl=proof.declaration('caller_return').replace('theorem caller_return','example',1)
        source=HEADER+decl+' := Doom.Proofs.OriginalTextureIteration.caller_return s f nonzero done safe returnWord\n'
        self.succeeds(source)
        for old in ['(nonzero : s.regs 3≠0)',
                    '(done : (Doom.Proofs.OriginalTextureIteration.iteration (Doom.Proofs.OriginalTextureIteration.prepared s)).pc=0x419cc)',
                    '(returnWord : load32 s.memory (s.regs 4)=0x34722)']:
            self.assertIn(old,source)
            self.rejects(source.replace(old,old.split(':')[0]+': True)'))
if __name__=='__main__':unittest.main()

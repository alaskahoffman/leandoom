"""Actual texture search continuation and repeated original comparisons."""
import sys,unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_texture_comparator as prior
ROOT=prior.prior.prior.proof.ROOT
HEADER='import Doom.Proofs.OriginalTextureSearch\n'+prior.prior.prior.proof.HEADER+'\nopen OriginalTextureSearch\n'
class AimTextureSearchTests(unittest.TestCase):
    lean=prior.AimTextureComparatorTests.lean
    succeeds=prior.AimTextureComparatorTests.succeeds
    rejects=prior.AimTextureComparatorTests.rejects
    def test_continuation_and_epilogue(self):
        self.assertTrue((ROOT/'Doom/Proofs/OriginalTextureSearch.lean').exists(),'texture search continuation implementation missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 2 ⟨s,f,0x34722⟩ (branch s) := branch_execution s f
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 7 ⟨s,f,0x34726⟩ (matched s f) := matched_execution s f
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 5 ⟨s,f,0x3472e⟩ (advanced s) := advance_execution s f
example (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 7 ⟨s,f,0x3473c⟩ (exhausted s f) := exhausted_execution s f
''')
    def test_repeated_comparison_and_outcomes(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤188, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (compared s) := comparison_execution s f
example (s : X86Memory.State) :
    (compared s).pc=0x34722 ∧ (compared s).core.regs 1=s.regs 1 ∧
      (compared s).core.regs 4=s.regs 4 ∧ (compared s).core.regs 6=s.regs 6 := comparison_registers s
example (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤202, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (round s) := round_execution s f
''')
    def test_terminating_search(self):
        self.succeeds(HEADER+'''
example (n : Nat) (s : X86Memory.State) (f : Option Flags)
    (positive : 0<n) (measure : (s.regs 1).toNat+n=2147483647) :
    ∃ k≤202*n, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (search n s f) := search_execution n s f positive measure
example (s : X86Memory.State) (f : Option Flags) (zero : s.regs 1=0) :
    ∃ k≤202*2147483647, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (search 2147483647 s f) := full_search_execution s f zero
''')
    def test_search_results_and_frame(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) :
    (compared s).core.regs 0=OriginalTextureComparator.compareBytes 8 (comparisonMemory s) (texture s) (s.regs 7) := comparison_result s
example (n : Nat) (s : X86Memory.State) (f : Option Flags) (a : Word)
    (callSafe : Apart a (s.regs 4-4)) (pushSafe : Apart a (s.regs 4-8)) :
    load32 (search n s f).core.memory a=load32 s.memory a := search_frame n s f a callSafe pushSafe
example (n : Nat) (s : X86Memory.State) (f : Option Flags)
    (positive : 0<n) (measure : (s.regs 1).toNat+n=2147483647) :
    (search n s f).pc=(load32 s.memory (s.regs 4+20)).toNat ∧
    (search n s f).core.regs 4=s.regs 4+24 ∧
    ((search n s f).core.regs 0=0xffffffff ∨ (search n s f).core.regs 0.toNat<2147483647) := by
  have h := search_return n s f positive measure
  exact h
'''.replace('(search n s f).core.regs 0.toNat','((search n s f).core.regs 0).toNat'))
    def test_named_lookup_wrapper(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimTextureSearch.lean').exists(),'named lookup/wrapper composition missing')
        self.succeeds('import Doom.Proofs.E1M1AimTextureSearch\n'+HEADER+'''
open E1M1AimTextureSearch
example (s : X86Memory.State) (f : Option Flags)
    (named : OriginalTextureDash.nameByte s≠0x2d)
    (positive : 0<(OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt) :
    ∃ k≤202*2147483647+13, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x346f0⟩ (namedResult s) := named_execution s f named positive
''')
    def test_wrapper_both_outcomes(self):
        self.succeeds('import Doom.Proofs.E1M1AimTextureSearch\n'+HEADER+'''
open E1M1AimTextureSearch
example (s : X86Memory.State) (f : Option Flags)
    (named : OriginalTextureDash.nameByte (OriginalTextureWrapper.search s f).core≠0x2d)
    (positive : 0<(OriginalTextureTable.count (OriginalTextureDash.prepared (OriginalTextureWrapper.search s f).core)).toInt)
    (dest : Word) (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ k≤202*2147483647+24, X86ByteRoutine.Prefix joined [] k ⟨s,f,0x34750⟩ (wrappedResult s f) := wrapper_execution s f named positive dest outside ret
''')
    def test_cumulative_certificate_and_mutations(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_texture_search.py').exists(),'search certificate missing')
        import verify_e1m1_aim_texture_search as proof
        import json,copy,re
        data,_=proof.previous.previous.previous.pinned_data();_,_,raw=proof.previous.previous.previous.extracted()
        for module in ['OriginalTextureSearch','E1M1AimTextureSearch']:
            self.assertEqual([n for m,n,_ in proof.CONTRACTS if m==module],re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('wrapper_execution_checked','absent')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.rejects(source.replace('0x85,0xc0,0x75,0x8','0x85,0xc0,0x74,0x8'))
        e=proof.table_evidence.extraction_support.extraction
        spec=json.loads((ROOT/'tests/reference/original-texture-search.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x76737'),('hex','85c07408'+spec['units']['continuation']['hex'][8:])]:
            bad=copy.deepcopy(spec);bad['units']['continuation'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
        for module,name,args,guard in [
            ('OriginalTextureSearch','search_execution','n s f positive measure','(measure : (s.regs 1).toNat+n=2147483647)'),
            ('OriginalTextureSearch','terminal_round','s stop','(stop : ¬continues s)'),
            ('E1M1AimTextureSearch','named_execution','s f named positive','(positive : 0<(OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt)')]:
            decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
            text='import Doom.Proofs.E1M1AimTextureSearch\n'+HEADER+decl+' := Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds(text)
            qualified=guard.replace('continues','Doom.Proofs.OriginalTextureSearch.continues')
            self.assertIn(qualified,text)
            self.rejects(text.replace(qualified,'('+guard.split(':')[0].strip('(')+' : True)'))
    def test_independent_cpu_searches(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_texture_search.py').exists(),'independent complete search checker missing')
        import subprocess,os,json
        result=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c',
          'import verify_e1m1_aim_texture_search as p,json; print(json.dumps(p.cross_check()))'],cwd=ROOT,
          env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=240)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        report=json.loads(result.stdout)
        self.assertGreater(report['repeated_cases'],0)
        self.assertGreater(report['exhausted_cases'],0)
        self.assertGreater(report['matched_cases'],0)
        self.assertGreater(report['alias_cases'],0)
        self.assertGreater(report['wrapper_cases'],0)
        self.assertTrue(report['all_registers_memory_ordered_writes'])
    def test_saved_register_restoration(self):
        self.succeeds('import Doom.Proofs.E1M1AimTextureSearch\n'+HEADER+'''
example (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (E1M1AimTextureSearch.namedResult s).core.regs r=s.regs r := E1M1AimTextureSearch.named_registers s r h0 h4
''')
if __name__=='__main__':unittest.main()

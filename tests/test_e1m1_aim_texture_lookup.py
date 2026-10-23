"""All original lookup branches; no supplied helper execution."""
import sys,unittest
sys.setrecursionlimit(max(sys.getrecursionlimit(),10000))
import test_e1m1_aim_texture_search as prior
ROOT=prior.ROOT
HEADER='import Doom.Proofs.E1M1AimTextureLookup\n'+prior.HEADER+'\nopen E1M1AimTextureLookup\n'
class AimTextureLookupTests(unittest.TestCase):
    lean=prior.AimTextureSearchTests.lean
    succeeds=prior.AimTextureSearchTests.succeeds
    rejects=prior.AimTextureSearchTests.rejects
    def test_all_inner_branches(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimTextureLookup.lean').exists(),'all-branch lookup implementation missing')
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (outside : dest.toNat<0x34741 ∨ 0x34747≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ k≤202*2147483647+19, X86ByteRoutine.Prefix E1M1AimTextureSearch.joined [] k
      ⟨s,f,0x346f0⟩ (lookup s) := lookup_execution s f dest outside ret
example (s : X86Memory.State) :
    (lookup s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (lookup s).core.regs 4=s.regs 4+4 := lookup_return s
example (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (lookup s).core.regs r=s.regs r := lookup_registers s r h0 h4
''')
    def test_wrapper_execution_and_derived_frames(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 s.memory (s.regs 4)=dest) :
    ∃ k≤202*2147483647+30, X86ByteRoutine.Prefix E1M1AimTextureSearch.joined [] k
      ⟨s,f,0x34750⟩ (wrapped s f) := wrapper_execution s f dest outside ret
example (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40], Apart a (s.regs 4-off)) :
    load32 (wrapped s f).core.memory a=load32 s.memory a := wrapper_frame s f a safe
example (s : X86Memory.State) (f : Option Flags) (success : (inner s f).core.regs 0≠0xffffffff)
    (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (wrapped s f).core.regs r=s.regs r := wrapper_registers s f success r h0 h4
''')
    def test_three_actual_calls_all_outcomes(self):
        self.assertTrue((ROOT/'Doom/Proofs/E1M1AimSideLookup.lean').exists(),'executed side caller missing')
        self.succeeds('import Doom.Proofs.E1M1AimSideLookup\n'+HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+14,
      X86ByteRoutine.Prefix E1M1AimSideLookup.joined [] k ⟨s,f,0x2e47e⟩
        (E1M1AimSideLookup.finished s f) := E1M1AimSideLookup.execution s f
example (s : X86Memory.State) (f : Option Flags) :
    (E1M1AimSideLookup.finished s f).pc=0x34760 ∨
    (E1M1AimSideLookup.finished s f).pc=0x2e4af := E1M1AimSideLookup.outcomes s f
''')
    def test_caller_frames_and_post_input(self):
        self.succeeds('import Doom.Proofs.E1M1AimSideLookup\n'+HEADER+'''
open E1M1AimSideLookup
example (s : X86Memory.State) (f : Option Flags) (ok : Returned s f) (r : Reg) (h0 : r≠0) :
    (finished s f).core.regs r=s.regs r := registers s f ok r h0
example (s : X86Memory.State) (f : Option Flags) (ok : Returned s f) (a : Word) (safe : Safe s a) :
    load32 (finished s f).core.memory a=load32 s.memory a := frame s f ok a safe
example (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : Safe s (s.regs 3+28)) (sectorSafe : Safe s 0x2c148) :
    E1M1AimSideEncoding.Input (finished s f).core side index sideBase sectorBase :=
      post_input s f ok side index sideBase sectorBase input sourceSafe sectorSafe
''')
    def test_actual_pointer_emission_and_latch(self):
        self.succeeds('import Doom.Proofs.E1M1AimSideLookup\n'+HEADER+'''
open E1M1AimSideLookup
example (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+29,
      X86ByteRoutine.Prefix iterationProgram [] k ⟨s,f,0x2e47e⟩ (iteration s f) := iteration_execution s f
example (s : X86Memory.State) (f : Option Flags) (ok : Returned s f)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : Safe s (s.regs 3+28)) (sectorSafe : Safe s 0x2c148) :
    E1M1NoiseImage.Realizes
      (E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress sideBase side) (E1M1AimSideEncoding.sectorAddress sectorBase index))
      (iteration s f).core.memory := emitted s f ok side index sideBase sectorBase input sourceSafe sectorSafe
''')
    def test_cumulative_certificate_and_negative_mutations(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_texture_lookup.py').exists(),'lookup certificate missing')
        import verify_e1m1_aim_texture_lookup as proof
        import re,copy,json
        data,_=proof.previous.previous.previous.previous.pinned_data()
        _,_,raw=proof.previous.previous.previous.previous.extracted()
        for module in ['E1M1AimTextureLookup','E1M1AimSideLookup']:
            self.assertEqual([n for m,n,_ in proof.CONTRACTS if m==module],re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output+'extra',output.replace('Quot.sound','sorryAx'),output.replace('iteration_execution_checked','absent')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        self.rejects(source.replace('0xe8,0xcd,0x62,0x0,0x0','0xe8,0xcc,0x62,0x0,0x0'))
        e=proof.previous.table_evidence.extraction_support.extraction
        spec=json.loads((ROOT/'tests/reference/original-side-textures.json').read_text())
        profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        bad=copy.deepcopy(spec);bad['units']['textures']['file_offset']=hex(int(bad['units']['textures']['file_offset'],16)+1)
        with self.assertRaises(ValueError):e.extract(binary,profile,bad)
        for module,name,args,guard in [
            ('E1M1AimTextureLookup','wrapper_registers','s f success r h0 h4','(success : (Doom.Proofs.E1M1AimTextureLookup.inner s f).core.regs 0≠0xffffffff)'),
            ('E1M1AimSideLookup','frame','s f ok a safe','(safe : Doom.Proofs.E1M1AimSideLookup.Safe s a)'),
            ('E1M1AimSideLookup','emitted','s f ok side index sideBase sectorBase input sourceSafe sectorSafe','(sourceSafe : Doom.Proofs.E1M1AimSideLookup.Safe s (s.regs 3+28))')]:
            decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
            text='import Doom.Proofs.E1M1AimSideLookup\n'+HEADER+decl+' := Doom.Proofs.'+module+'.'+name+' '+args+'\n'
            self.succeeds(text);self.assertIn(guard,text)
            self.rejects(text.replace(guard,guard.split(':')[0]+': True)'))
    def test_independent_cpu_connected_calls(self):
        self.assertTrue((ROOT/'scripts/verify_e1m1_aim_texture_lookup.py').exists(),'connected CPU checker missing')
        import subprocess,os,json
        run=subprocess.run([str(ROOT/'.tools/x86-check/bin/python'),'-c','import verify_e1m1_aim_texture_lookup as p,json; print(json.dumps(p.cross_check()))'],cwd=ROOT,env={**os.environ,'PYTHONPATH':'scripts'},capture_output=True,text=True,timeout=300)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        report=json.loads(run.stdout)
        for name in ['dash_lookups','nonpositive_lookups','positive_lookups','complete_three_calls','error_first','error_second','error_third','wrapping_stack_cases','alias_cases','continued_cases','finished_cases','body_cases']:
            self.assertGreater(report[name],0,name)
        self.assertTrue(report['all_registers_memory_ordered_writes'])
    def test_full_body_from_offset_loads(self):
        self.succeeds('import Doom.Proofs.E1M1AimSideLookup\n'+HEADER+'''
example (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+36,
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k ⟨s,f,0x2e46a⟩
        (E1M1AimSideLookup.iteration (OriginalSideAdvance.prepared s).core none) :=
          E1M1AimSideLookup.body_execution s f
''')
if __name__=='__main__':unittest.main()

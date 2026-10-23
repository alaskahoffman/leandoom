"""Side-loop control flow and emitted-pointer preservation at exact CALL boundary."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_side_encoding as prior
import verify_e1m1_aim_side_advance as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimSideAdvance\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\n'
FIXTURE=HEADER+'''
namespace SideAdvanceFixture
 def state (total counter : Word) : X86Memory.State :=
   ⟨fun r => if r=2 then 0x50000 else if r=3 then 0xa0000 else if r=4 then 0xb0000 else if r=5 then counter else 0,
    store32 (store32 (fun _ => 0) 0x2c148 0x60000) 0x2c11c total⟩
 theorem input (total counter : Word) : E1M1AimSideEncoding.Input (state total counter) 0 0 0x50000 0x60000 := by
   refine ⟨by simp [state],?_,?_,?_,by decide⟩
   · intro x hx
     simp only [E1M1NoiseImage.half,List.mem_cons,List.not_mem_nil,or_false] at hx
     rcases hx with rfl|rfl <;> simp [state,store32]
   · simp [state,load32,store32]
   · change Apart 0x2c148 0xb0000
     unfold Apart; decide
 theorem safe (total counter : Word) : Apart 0x2c11c ((state total counter).regs 4) ∧
     Apart 0x2c11c ((state total counter).regs 2+14) := by
   change Apart 0x2c11c 0xb0000 ∧ Apart 0x2c11c (0x50000+14)
   constructor <;> unfold Apart <;> decide
'''
class AimSideAdvanceTests(unittest.TestCase):
    lean=prior.AimSideEncodingTests.lean
    succeeds=prior.AimSideEncodingTests.succeeds
    rejects=prior.AimSideEncodingTests.rejects
    mutations=prior.AimSideEncodingTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_full_certificate_authentication_and_strict_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();scan=proof.previous.evidence.scan_data();side=proof.previous.side_data();advance=proof.advance_data()
        self.assertEqual(len(proof.combined_units(spec['units'],scan[1],side[1],advance[1])),64)
        source=proof.certificate(data,raw,scan,side,advance)
        output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimSideAdvance.latch_checked','missing'),
                    output.replace('E1M1AimSideAdvance.bounded_finished_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        for old,new in [('0x39,0xc5,0x7c,0x8d','0x39,0xc5,0x7d,0x8d'),('0x89,0x42,0x4,0x89,0xc8','0x89,0x42,0x5,0x89,0xc8')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))
    def test_extraction_rejects_changed_file_mapping_and_relocation(self):
        e=proof.previous.side.extraction
        spec=json.loads((ROOT/'tests/reference/original-side-advance.json').read_text());profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x704e4'),('relocations',[])]:
            bad=copy.deepcopy(spec);bad['units']['latch'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
    def test_continuation_and_finish_carry_actual_pointer_bytes(self):
        self.succeeds(FIXTURE+'''
example : X86Routine.run OriginalSideAdvance.program [0x2e47e,0x2e4dd] 22 ⟨state 2 0,none,0x2e4af⟩=
    some (OriginalSideAdvance.prepared (OriginalSideAdvance.result (state 2 0)).core) ∧
    E1M1NoiseImage.Realizes (E1M1NoiseImage.word (0x50000+14) 0x60000)
    (OriginalSideAdvance.prepared (OriginalSideAdvance.result (state 2 0)).core).core.memory := by
  exact E1M1AimSideAdvance.bounded_continuation (state 2 0) none 0 0 0 2 0x50000 0x60000
    (input 2 0) (by decide) (by decide) (by decide) (by decide) (safe 2 0).1 (safe 2 0).2
example : X86Routine.run OriginalSideAdvance.program [0x2e46a,0x2e4dd] 15 ⟨state 1 0,none,0x2e4af⟩=
    some (OriginalSideAdvance.result (state 1 0)) ∧ (OriginalSideAdvance.result (state 1 0)).pc=0x2e4dd ∧
    E1M1NoiseImage.Realizes (E1M1NoiseImage.word (0x50000+14) 0x60000)
    (OriginalSideAdvance.result (state 1 0)).core.memory := by
  exact E1M1AimSideAdvance.bounded_finished (state 1 0) none 0 0 0 1 0x50000 0x60000
    (input 1 0) (by decide) (by decide) (by decide) (by decide) (safe 1 0).1 (safe 1 0).2
end SideAdvanceFixture
''')
    def test_signed_overflow_and_zero_count_match_original_gate(self):
        self.succeeds(FIXTURE+'''
example : (OriginalSideAdvance.result (state 0 0)).pc=0x2e4dd := by decide
example : (OriginalSideAdvance.result (state 0xffffffff 0)).pc=0x2e4dd := by decide
example : (OriginalSideAdvance.result (state 1 0x7fffffff)).pc=0x2e46a := by decide
example : (OriginalSideAdvance.result (state 1 0xffffffff)).pc=0x2e46a := by decide
end SideAdvanceFixture
''')
    def test_count_is_read_after_scratch_write(self):
        self.succeeds(FIXTURE+'''
def clobbered : X86Memory.State := {state 2 0 with regs:=fun r => if r=4 then 0x2c11c else (state 2 0).regs r}
example : load32 clobbered.memory 0x2c11c=2 ∧
    load32 (OriginalSideAdvance.result clobbered).core.memory 0x2c11c=0 ∧
    (OriginalSideAdvance.result clobbered).pc=0x2e4dd := by decide
end SideAdvanceFixture
''')
    def test_second_offset_uses_memory_after_first_store(self):
        self.succeeds(HEADER+'''
def aliasState : X86Memory.State := ⟨fun r => if r=3 then 0x40000 else if r=2 then 0x40002 else 0,
  store32 (fun _ => 0) 0x40000 0x12340001⟩
example : load16 aliasState.memory (aliasState.regs 3+2)=0x1234 ∧
    OriginalSideAdvance.second aliasState=0 := by decide
example : load32 (OriginalSideAdvance.prepared aliasState).core.memory (aliasState.regs 2+4)=0 := by decide
''')
    def test_pointer_preservation_needs_no_nonwrapping_assumption(self):
        self.succeeds(HEADER+'''
example (s : X86Memory.State) (atEnd : s.regs 2=0xfffffff0) :
    load32 (OriginalSideAdvance.prepared (OriginalSideAdvance.result s).core).core.memory 0xfffffffe=
    load32 (OriginalSideAdvance.result s).core.memory 0xfffffffe := by
  have h := E1M1AimSideAdvance.next_offsets_preserve s
  rw [atEnd] at h
  exact h
''')
    def test_signed_bounds_and_count_separation_are_essential(self):
        self.mutations(self.contract('E1M1AimSideAdvance','bounded_branch'),[
          ('(small : total<2147483648)','(small : True)'),('(inside : i<total)','(inside : True)'),
          ('(scratchSafe : Apart 0x2c11c (s.regs 4))','(scratchSafe : True)'),
          ('(pointerSafe : Apart 0x2c11c (s.regs 2+14))','(pointerSafe : True)')])
    def test_continuation_requires_branch_but_no_emitted_pointer_frame(self):
        self.mutations(self.contract('OriginalSideAdvance','continued_execution'),[
          ('(next : (Doom.Proofs.OriginalSideAdvance.result s).pc=0x2e46a)','(next : True)')])
        self.succeeds(self.contract('E1M1AimSideAdvance','continuing_emitted'))
        decl=proof.declaration('E1M1AimSideAdvance','continuing_emitted')
        self.assertNotIn('Kept',decl);self.assertNotIn('Apart',decl)
if __name__=='__main__':unittest.main()

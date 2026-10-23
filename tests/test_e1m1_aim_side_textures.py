"""Exact caller writes and genuine-path premises at the texture lookup seam."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_side_advance as prior
import verify_e1m1_aim_side_textures as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimSideTextures\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\n'
FIXTURE="""import Doom.Proofs.E1M1AimSideTextures
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalSideTextures
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace TextureJoinFixture
/-- Test-only return instruction, NOT a model/certificate of DOS texture lookup. -/
def q (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if pc=0x34750 then some (.ret,1) else OriginalSideTextures.program pc
 theorem agree (pc : Nat) (h : OriginalSideTextures.program pc≠none) : q pc=OriginalSideTextures.program pc := by
  by_cases eq : pc=0x34750
  · subst pc; exact False.elim (h (by decide))
  · simp [q,eq]
 def returned (s : X86Control.State) : X86Control.State :=
   ⟨put s.core 4 (s.core.regs 4+4),s.flags,(load32 s.core.memory (s.core.regs 4)).toNat⟩
 theorem ret_path (s : X86Control.State) (pc : s.pc=0x34750) :
     X86Routine.Prefix q [] 1 s (returned s) := by
   exact .step (by simp) (by rw [pc]; rfl) (by rfl) (.nil _)
 def initial : X86Memory.State := ⟨fun r => if r=0 then 0x12345678 else if r=2 then 0x50012 else if r=4 then 0x80000
   else if r=7 then 0xabcdef01 else if r=6 then 0x10203456 else 0,store32 (fun _ => 0) (0x50000+14) 0x60000⟩
 def a := returned (firstCall initial none)
 def b := returned (secondCall a.core a.flags)
 def c := returned (thirdCall b.core b.flags)
 theorem pa : X86Routine.Prefix q [] 1 (firstCall initial none) ⟨a.core,a.flags,0x2e483⟩ := by
   exact ret_path _ rfl
 theorem pb : X86Routine.Prefix q [] 1 (secondCall a.core a.flags) ⟨b.core,b.flags,0x2e494⟩ := by
   exact ret_path _ rfl
 theorem pc : X86Routine.Prefix q [] 1 (thirdCall b.core b.flags) ⟨c.core,c.flags,0x2e4a5⟩ := by
   exact ret_path _ rfl
 example : ∃ n≤17, X86Routine.Prefix q [] n ⟨initial,none,0x2e47e⟩ (finished c.core c.flags) := by
   exact E1M1AimSideTextures.caller_path q agree initial a.core b.core c.core none a.flags b.flags c.flags 1 1 1 pa pb pc
 example : E1M1NoiseImage.Realizes (E1M1NoiseImage.word (0x50000+14) 0x60000) (finished c.core c.flags).core.memory := by
   apply E1M1AimSideTextures.caller_encoding initial a.core b.core c.core none a.flags b.flags c.flags
   · unfold E1M1NoiseImage.Realizes; decide
   · unfold Apart; decide
   · exact E1M1AimSideTextures.previous_safe a.core 0x50000 0x80000 8 (by decide) (by decide) (by decide)
       (by unfold Apart; decide) (by unfold Apart; decide)
   · exact E1M1AimSideTextures.previous_safe b.core 0x50000 0x80000 10 (by decide) (by decide) (by decide)
       (by unfold Apart; decide) (by unfold Apart; decide)
   · unfold Apart; decide
   · exact E1M1AimSideTextures.previous_fields 0x50000 12 (by decide)
   · rfl
   · rfl
   · rfl
 example : load16 (finished c.core c.flags).core.memory (0x50012+8)=0x5678 ∧
     load16 (finished c.core c.flags).core.memory (0x50012+10)=0xef01 ∧
     load16 (finished c.core c.flags).core.memory (0x50012+12)=0x3456 := by decide
end TextureJoinFixture
"""
class AimSideTexturesTests(unittest.TestCase):
    lean=prior.AimSideAdvanceTests.lean
    succeeds=prior.AimSideAdvanceTests.succeeds
    rejects=prior.AimSideAdvanceTests.rejects
    mutations=prior.AimSideAdvanceTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_full_certificate_and_strict_inherited_audit(self):
        data,_=proof.pinned_data();spec,_,raw=proof.extracted();scan=proof.previous.previous.evidence.scan_data();side=proof.previous.previous.side_data();advance=proof.previous.advance_data();textures=proof.texture_data()
        self.assertEqual(len(proof.combined_units(spec['units'],scan[1],side[1],advance[1],textures[1])),65)
        source=proof.certificate(data,raw,scan,side,advance,textures)
        output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimSideTextures.textures_checked','missing'),
                    output.replace('E1M1AimSideTextures.linked_path_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        for old,new in [('0xe8,0xcd,0x62','0xe8,0xcc,0x62'),('0x66,0x89,0x42,0x8','0x66,0x89,0x42,0x9')]:
            self.assertIn(old,source);self.rejects(source.replace(old,new))
    def test_constructive_join_with_explicit_test_only_return_paths(self):
        self.succeeds(FIXTURE)
    def test_helper_paths_and_exact_return_addresses_are_required(self):
        source=self.contract('E1M1AimSideTextures','caller_path')
        self.mutations(source,[
          ('(lookupA : X86Routine.Prefix q [] na (Doom.Proofs.OriginalSideTextures.firstCall s f) ⟨a,fa,0x2e483⟩)','(lookupA : True)'),
          ('⟨b,fb,0x2e494⟩','⟨b,fb,0x2e483⟩')])
    def test_lookup_memory_frames_cannot_be_omitted(self):
        self.mutations(self.contract('E1M1AimSideTextures','caller_frame'),[
          ('(lookupA : load32 a.memory address=load32 (Doom.Proofs.OriginalSideTextures.firstCall s f).core.memory address)','(lookupA : True)'),
          ('(lookupC : load32 c.memory address=load32 (Doom.Proofs.OriginalSideTextures.thirdCall b fb).core.memory address)','(lookupC : True)'),
          ('(finalScratch : Apart address (c.regs 4))','(finalScratch : True)')])
    def test_actual_call_push_can_overwrite_new_texture_field(self):
        self.succeeds(HEADER+"""
def overlapping : X86Memory.State := ⟨fun r => if r=0 then 0x12345678 else if r=2 then 0x50000 else if r=4 then 0x5000c else 0,fun _ => 0⟩
example : load16 (OriginalSideTextures.stored overlapping 8).memory 0x50008=0x5678 ∧
    load16 (OriginalSideTextures.secondCall overlapping none).core.memory 0x50008=0xe494 := by decide
""")
    def test_full_word_scratch_and_low_halfword_field_are_distinct(self):
        self.succeeds(HEADER+"""
def ordinary : X86Memory.State := ⟨fun r => if r=0 then 0xdead5678 else if r=2 then 0x50000 else if r=4 then 0x80000 else 0,fun _ => 0⟩
example : load32 (OriginalSideTextures.stored ordinary 12).memory 0x80000=0xdead5678 ∧
    load16 (OriginalSideTextures.stored ordinary 12).memory (0x50000+12)=0x5678 := by decide
example (s : X86Memory.State) (f : Option Flags) :
    load32 (OriginalSideTextures.thirdCall s f).core.memory ((OriginalSideTextures.thirdCall s f).core.regs 4)=0x2e4a5 := by
  exact (OriginalSideTextures.return_addresses s f).2.2
""")
    def test_previous_pointer_field_separation_includes_wraparound(self):
        self.succeeds(HEADER+"""
example : HalfMemory.Separate 4 2 (0xfffffffa+14) (0xfffffffa+18+10) := by
  exact E1M1AimSideTextures.previous_fields 0xfffffffa 10 (by decide)
""")
        self.mutations(self.contract('E1M1AimSideTextures','previous_fields'),[
          ('(member : off∈[(8#32),10,12])','(member : True)')])
    def test_final_pointer_join_keeps_helper_and_post_texture_input_obligations(self):
        source=self.contract('E1M1AimSideTextures','linked_path');self.succeeds(source)
        self.assertIn('(lookupA : X86Routine.Prefix',source)
        self.assertIn('(lookupB : X86Routine.Prefix',source)
        self.assertIn('(lookupC : X86Routine.Prefix',source)
        self.mutations(source,[
          ('(input : Doom.Proofs.E1M1AimSideEncoding.Input (Doom.Proofs.OriginalSideTextures.stored c 12) side sectorIndex sideBase sectorBase)','(input : True)')])
    def test_extraction_rejects_wrong_mapping_and_invented_relocation(self):
        e=proof.previous.previous.side.extraction
        spec=json.loads((ROOT/'tests/reference/original-side-textures.json').read_text());profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x70493'),('relocations',[dict(offset=1,object=3,target='0x62cd')])]:
            bad=copy.deepcopy(spec);bad['units']['textures'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
if __name__=='__main__':unittest.main()

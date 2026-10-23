"""Original wrapper and explicit inner-search obligations; no lookup oracle."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_side_textures as prior
import verify_e1m1_aim_texture_wrapper as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimTextureWrapper\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\nset_option maxHeartbeats 1600000\n'
class AimTextureWrapperTests(unittest.TestCase):
    lean=prior.AimSideTexturesTests.lean
    succeeds=prior.AimSideTexturesTests.succeeds
    rejects=prior.AimSideTexturesTests.rejects
    mutations=prior.AimSideTexturesTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_full_certificate_and_strict_inherited_audit(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted()
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimTextureWrapper.wrapper_checked','missing'),
                    output.replace('E1M1AimTextureWrapper.caller_path_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        self.assertIn('0x53,0x52,0x89,0xc2',source)
        self.rejects(source.replace('0x53,0x52,0x89,0xc2','0x53,0x51,0x89,0xc2'))
    def test_real_inner_path_and_success_condition_required(self):
        self.mutations(self.contract('E1M1AimTextureWrapper','success_path'),[
          ('(inner : X86Routine.Prefix q [] n (Doom.Proofs.OriginalTextureWrapper.search s f) ⟨t,g,0x34759⟩)','(inner : True)'),
          ('(found : t.regs 0≠(0xffffffff#32))','(found : True)'),
          ('⟨t,g,0x34759⟩','⟨t,g,0x34760⟩')])
    def test_return_pc_and_saved_words_required(self):
        self.mutations(self.contract('E1M1AimTextureWrapper','caller_path'),[
          ('(ret : load32 t.memory (t.regs 4+8)=dest)','(ret : True)'),
          ('(t.regs 4+8)=dest','(t.regs 4+4)=dest')])
        self.mutations(self.contract('E1M1AimTextureWrapper','saved_registers'),[
          ('(stack : t.regs 4=s.regs 4-8)','(stack : True)'),
          ('(edx : load32 t.memory (s.regs 4-8)=load32 (Doom.Proofs.OriginalTextureWrapper.search s f).core.memory (s.regs 4-8))','(edx : True)')])
    def test_wrapper_word_frame_requires_all_three_stack_slots_and_inner_frame(self):
        self.mutations(self.contract('E1M1AimTextureWrapper','wrapper_frame'),[
          ('(call : Apart a (s.regs 4-12))','(call : True)'),
          ('(inner : load32 t.memory a=load32 (Doom.Proofs.OriginalTextureWrapper.search s f).core.memory a)','(inner : True)')])
    def test_zero_is_success_minus_one_is_error_and_return_memory_is_read_only(self):
        self.succeeds(HEADER+'''
def s (v : Word) : X86Memory.State := ⟨fun r => if r=0 then v else if r=4 then 0x80000 else 0,
  store32 (store32 (store32 (fun _ => 0) 0x80000 0x1234) 0x80004 0x5678) 0x80008 0x2e483⟩
example : (OriginalTextureWrapper.choice (s 0)).pc=0x3476e ∧
    (OriginalTextureWrapper.choice (s 0xffffffff)).pc=0x34760 := by decide
example : X86Routine.run OriginalTextureWrapper.program [0x2e483] 4
    ⟨(OriginalTextureWrapper.choice (s 0)).core,none,0x3476e⟩=
    some (OriginalTextureWrapper.result (OriginalTextureWrapper.choice (s 0)).core none) := by
  apply OriginalTextureWrapper.return_execution _ _ 0x2e483 <;> decide
example : (OriginalTextureWrapper.result (OriginalTextureWrapper.choice (s 0)).core none).core.regs 0=0 ∧
    (OriginalTextureWrapper.result (OriginalTextureWrapper.choice (s 0)).core none).core.regs 2=0x1234 ∧
    (OriginalTextureWrapper.result (OriginalTextureWrapper.choice (s 0)).core none).core.regs 3=0x5678 ∧
    (OriginalTextureWrapper.result (OriginalTextureWrapper.choice (s 0)).core none).core.regs 4=0x8000c := by decide
example : (OriginalTextureWrapper.result (s 0) none).core.memory=(s 0).memory := rfl
''')
    def test_saved_slots_and_return_word_survive_address_wraparound(self):
        self.succeeds(HEADER+'''
def s : X86Memory.State := ⟨fun r => if r=4 then 3 else if r=2 then 0x12345678 else if r=3 then 0xabcdef01 else 0,
  store32 (fun _ => 0) 3 0x2e494⟩
example : load32 (OriginalTextureWrapper.search s none).core.memory (s.regs 4-8)=s.regs 2 ∧
    load32 (OriginalTextureWrapper.search s none).core.memory (s.regs 4-4)=s.regs 3 ∧
    load32 (OriginalTextureWrapper.search s none).core.memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  exact OriginalTextureWrapper.saved_slots s none
example : load32 (OriginalTextureWrapper.search s none).core.memory 3=0x2e494 := by decide
example : (OriginalTextureWrapper.search s none).core.regs 4=0xfffffff7 := by decide
''')
    def test_extraction_rejects_changed_byte_mapping_and_data_fixup(self):
        e=proof.previous.previous.previous.side.extraction
        spec=json.loads((ROOT/'tests/reference/original-texture-wrapper.json').read_text());profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x76765'),('relocations',[]),('hex','90'+spec['units']['wrapper']['hex'][2:])]:
            bad=copy.deepcopy(spec);bad['units']['wrapper'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
if __name__=='__main__':unittest.main()

"""Real dash execution, shared restoration, and explicit named-search boundary."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_texture_wrapper as prior
import verify_e1m1_aim_texture_dash as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimTextureDash\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\nset_option maxHeartbeats 1600000\n'
FIXTURE='''
def q (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x346f0≤pc ∧ pc<0x34700) ∨ (0x34741≤pc ∧ pc<0x34747)
  then OriginalTextureDash.program pc else OriginalTextureWrapper.program pc
 theorem dash_agrees (pc : Nat) (h : OriginalTextureDash.program pc≠none) : q pc=OriginalTextureDash.program pc := by
  by_cases a : 0x346f0≤pc ∧ pc<0x34700
  · simp [q,a]
  by_cases b : 0x34741≤pc ∧ pc<0x34747
  · simp [q,b]
  · simp [OriginalTextureDash.program,OriginalTextureDash.bytesProgram,a,b] at h
 theorem wrapper_agrees (pc : Nat) (h : OriginalTextureWrapper.program pc≠none) : q pc=OriginalTextureWrapper.program pc := by
  have bounds : 0x34750≤pc ∧ pc<0x34773 := by
    by_cases b : 0x34750≤pc ∧ pc<0x34773
    · exact b
    · simp [OriginalTextureWrapper.program,OriginalTextureWrapper.bytesProgram,b] at h
  have outside : ¬((0x346f0≤pc ∧ pc<0x34700) ∨ (0x34741≤pc ∧ pc<0x34747)) := by omega
  simp [q,outside]
def s (sp : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x61000 else if r=4 then sp else
    if r=2 then 0x12345678 else if r=3 then 0x87654321 else if r=7 then 0x41424344 else 0,
    store32 (fun a => if a=0x61000 then 0x2d else 0) sp 0x2e483⟩
'''
class AimTextureDashTests(unittest.TestCase):
    lean=prior.AimTextureWrapperTests.lean
    succeeds=prior.AimTextureWrapperTests.succeeds
    rejects=prior.AimTextureWrapperTests.rejects
    mutations=prior.AimTextureWrapperTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_full_certificate_and_strict_inherited_audit(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted()
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimTextureDash.restore_checked','missing'),
                    output.replace('E1M1AimTextureDash.wrapper_path_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        self.assertIn('0x53,0x51,0x52,0x56,0x57',source)
        self.rejects(source.replace('0x53,0x51,0x52,0x56,0x57','0x53,0x51,0x52,0x56,0x56'))
    def test_complete_original_wrapper_executes_without_helper_fixture(self):
        self.succeeds(HEADER+FIXTURE+'''
example : ∃ n≤27, X86Routine.Prefix q [] n ⟨s 0x80000,none,0x34750⟩
    ⟨(E1M1AimTextureDash.completed (s 0x80000) none).core,
      (E1M1AimTextureDash.completed (s 0x80000) none).flags,0x2e483⟩ := by
  apply E1M1AimTextureDash.wrapper_path q dash_agrees wrapper_agrees (s 0x80000) none
    (by decide) 0x2e483 (by decide) (by decide)
example : ∃ n≤27, X86Routine.Prefix q [] n ⟨s 3,none,0x34750⟩
    ⟨(E1M1AimTextureDash.completed (s 3) none).core,
      (E1M1AimTextureDash.completed (s 3) none).flags,0x2e483⟩ := by
  apply E1M1AimTextureDash.wrapper_path q dash_agrees wrapper_agrees (s 3) none
    (by decide) 0x2e483 (by decide) (by decide)
''')
    def test_dash_guard_return_word_and_program_agreement_are_required(self):
        source=self.contract('E1M1AimTextureDash','wrapper_path')
        self.assertNotIn('inner : X86Routine.Prefix',source)
        self.mutations(source,[
          ('(dash : Doom.Proofs.OriginalTextureDash.nameByte (OriginalTextureWrapper.search s f).core=(0x2d#8))','(dash : True)'),
          ('(ret : load32 s.memory (s.regs 4)=dest)','(ret : True)'),
          ('(wrapper : ∀ pc, OriginalTextureWrapper.program pc≠none → q pc=OriginalTextureWrapper.program pc)','(wrapper : True)')])
    def test_aliasing_is_decided_after_register_pushes(self):
        self.succeeds(HEADER+'''
def aliased (value : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x7ffec else if r=4 then 0x80000 else if r=7 then value else 0,
    fun a => if a=0x7ffec then 0x2d else 0⟩
example : (aliased 0x41).memory ((aliased 0x41).regs 0)=0x2d ∧
    OriginalTextureDash.nameByte (aliased 0x41)=0x41 ∧
    (OriginalTextureDash.gate (aliased 0x41)).pc=0x34700 := by decide
example : (OriginalTextureDash.gate (aliased 0x2d)).pc=0x346fc := by decide
''')
    def test_stack_frame_requires_separation_and_saved_slots_are_not_unchanged(self):
        self.mutations(self.contract('E1M1AimTextureDash','wrapper_frame'),[
          ('(safe : ∀ off∈[(4#32),8,12,16,20,24,28,32], Apart a (s.regs 4-off))','(safe : True)')])
        self.succeeds(HEADER+FIXTURE+'''
example : load32 (E1M1AimTextureDash.completed (s 0x80000) none).core.memory 0x7ffe0=0x41424344 := by decide
example : load32 (s 0x80000).memory 0x7ffe0=0 := by decide
''')
    def test_shared_return_restores_arbitrary_values_without_touching_memory(self):
        self.succeeds(HEADER+'''
def t : X86Memory.State := ⟨fun r => if r=0 then 0xfeedbeef else if r=4 then 0x80000 else 0,
  store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0)
    0x80000 7) 0x80004 6) 0x80008 2) 0x8000c 1) 0x80010 3) 0x80014 0x34759⟩
example : X86Routine.run OriginalTextureDash.program [0x34759] 6 ⟨t,none,0x34741⟩=
    some (OriginalTextureDash.result t none) := by
  apply OriginalTextureDash.return_execution _ _ 0x34759 <;> decide
example : ((OriginalTextureDash.result t none).core.regs 0,
    (OriginalTextureDash.result t none).core.regs 7,(OriginalTextureDash.result t none).core.regs 6,
    (OriginalTextureDash.result t none).core.regs 2,(OriginalTextureDash.result t none).core.regs 1,
    (OriginalTextureDash.result t none).core.regs 3,(OriginalTextureDash.result t none).core.regs 4)=
    (0xfeedbeef,7,6,2,1,3,0x80018) := by decide
example : (OriginalTextureDash.result t none).core.memory=t.memory := rfl
''')
    def test_extraction_rejects_changed_mapping_and_invented_fixup(self):
        e=proof.previous.previous.previous.previous.side.extraction
        spec=json.loads((ROOT/'tests/reference/original-texture-dash.json').read_text());profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x76705'),('relocations',[dict(offset=1,object=3,target='0x1234')]),('hex','90'+spec['units']['entry']['hex'][2:])]:
            bad=copy.deepcopy(spec);bad['units']['entry'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
if __name__=='__main__':unittest.main()

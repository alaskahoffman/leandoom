"""Named-search gate, original comparison boundary and real empty-table return."""
import copy,json,re,unittest
from pathlib import Path
import test_e1m1_aim_texture_dash as prior
import verify_e1m1_aim_texture_table as proof
ROOT=Path(__file__).resolve().parents[1]
HEADER='import Doom.Proofs.E1M1AimTextureTable\n'+proof.HEADER+'\nset_option backward.isDefEq.respectTransparency false\nset_option maxRecDepth 32768\nset_option maxHeartbeats 1600000\n'
FIXTURE=prior.FIXTURE+'''
def combined (pc : Nat) : Option (X86Routine.Op × Nat) :=
  if (0x34700≤pc ∧ pc<0x34722) ∨ (0x3473c≤pc ∧ pc<0x34741)
  then OriginalTextureTable.program pc else q pc
 theorem table_code (pc : Nat) (h : OriginalTextureTable.program pc≠none) : combined pc=OriginalTextureTable.program pc := by
  by_cases a : 0x34700≤pc ∧ pc<0x34722
  · simp [combined,a]
  by_cases b : 0x3473c≤pc ∧ pc<0x34741
  · simp [combined,b]
  · simp [OriginalTextureTable.program,OriginalTextureTable.bytesProgram,a,b] at h
 theorem dash_code (pc : Nat) (h : OriginalTextureDash.program pc≠none) : combined pc=OriginalTextureDash.program pc := by
  have bounds : (0x346f0≤pc ∧ pc<0x34700) ∨ (0x34741≤pc ∧ pc<0x34747) := by
    by_cases a : 0x346f0≤pc ∧ pc<0x34700
    · exact Or.inl a
    by_cases b : 0x34741≤pc ∧ pc<0x34747
    · exact Or.inr b
    · simp [OriginalTextureDash.program,OriginalTextureDash.bytesProgram,a,b] at h
  have outside : ¬((0x34700≤pc ∧ pc<0x34722) ∨ (0x3473c≤pc ∧ pc<0x34741)) := by omega
  simpa [combined,outside] using dash_agrees pc h
 theorem wrapper_code (pc : Nat) (h : OriginalTextureWrapper.program pc≠none) : combined pc=OriginalTextureWrapper.program pc := by
  have bounds : 0x34750≤pc ∧ pc<0x34773 := by
    by_cases b : 0x34750≤pc ∧ pc<0x34773
    · exact b
    · simp [OriginalTextureWrapper.program,OriginalTextureWrapper.bytesProgram,b] at h
  have outside : ¬((0x34700≤pc ∧ pc<0x34722) ∨ (0x3473c≤pc ∧ pc<0x34741)) := by omega
  simpa [combined,outside] using wrapper_agrees pc h
 def sample (sp value : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600100 else if r=4 then sp else if r=7 then 1 else 0,
    store32 (store32 (fun a => if a=0x600100 then 0x41 else 0) 0x300e4 value) sp 0x2e483⟩
'''
class AimTextureTableTests(unittest.TestCase):
    lean=prior.AimTextureDashTests.lean
    succeeds=prior.AimTextureDashTests.succeeds
    rejects=prior.AimTextureDashTests.rejects
    mutations=prior.AimTextureDashTests.mutations
    def contract(self,module,name):
        args=next(a for m,n,a in proof.CONTRACTS if (m,n)==(module,name))
        decl=proof.declaration(module,name).replace('theorem '+name,'example',1)
        return HEADER+decl+' :=\n  Doom.Proofs.'+module+'.'+name+' '+args+'\n'
    def test_full_certificate_and_strict_inherited_audit(self):
        data,_=proof.pinned_data();_,_,raw=proof.extracted()
        source=proof.certificate(data,raw);output=self.succeeds(source);proof.audit(output)
        for bad in [output.replace('Quot.sound','sorryAx'),output+'extra',
                    output.replace('ExtractedAimTextureTable.table_checked','missing'),
                    output.replace('E1M1AimTextureTable.wrapper_empty_path_checked','missing')]:
            with self.assertRaises(ValueError):proof.audit(bad)
        for module,names in proof.GROUPS.items():
            self.assertEqual(names,re.findall(r'^theorem (\w+) ',(ROOT/f'Doom/Proofs/{module}.lean').read_text(),re.M))
        self.assertIn('0x8b,0x15,0xe4,0x0,0x3,0x0',source)
        self.rejects(source.replace('0x8b,0x15,0xe4,0x0,0x3,0x0','0x8b,0x15,0xe0,0x0,0x3,0x0'))
    def test_nonpositive_original_path_composes_including_wrapping_stack(self):
        self.succeeds(HEADER+FIXTURE+'''
example : ∃ n≤26, X86Routine.Prefix combined [] n ⟨sample 3 0xffffffff,none,0x34750⟩
    ⟨(OriginalTextureWrapper.choice (E1M1AimTextureTable.emptyResult
        (OriginalTextureWrapper.search (sample 3 0xffffffff) none).core).core).core,
      (OriginalTextureWrapper.choice (E1M1AimTextureTable.emptyResult
        (OriginalTextureWrapper.search (sample 3 0xffffffff) none).core).core).flags,0x34760⟩ := by
  apply E1M1AimTextureTable.wrapper_empty_path combined dash_code table_code wrapper_code <;> decide
example : ∃ n≤19, X86Routine.Prefix combined [] n ⟨sample 0x80000 0,none,0x346f0⟩
    (E1M1AimTextureTable.emptyResult (sample 0x80000 0)) := by
  apply E1M1AimTextureTable.empty_path combined dash_code table_code _ _ (by decide) (by decide)
    0x2e483 (by decide) (by decide)
''')
    def test_positive_path_reaches_real_call_and_requires_positive_count(self):
        self.succeeds(HEADER+FIXTURE+'''
example : ∃ n≤18, X86Routine.Prefix combined [] n ⟨sample 0x80000 1,none,0x346f0⟩
    (OriginalTextureTable.comparison (OriginalTextureTable.tested
      (OriginalTextureDash.prepared (sample 0x80000 1))).core) := by
  apply E1M1AimTextureTable.first_comparison_path combined dash_code table_code <;> decide
''')
        self.mutations(self.contract('E1M1AimTextureTable','first_comparison_path'),[
          ('(positive : 0<(Doom.Proofs.OriginalTextureTable.count (Doom.Proofs.OriginalTextureDash.prepared s)).toInt)','(positive : True)')])
    def test_nonpositive_guard_name_and_program_premises_are_required(self):
        source=self.contract('E1M1AimTextureTable','wrapper_empty_path');self.assertNotIn('inner : X86Routine.Prefix',source)
        self.mutations(source,[
          ('(empty : (Doom.Proofs.OriginalTextureTable.count (Doom.Proofs.OriginalTextureDash.prepared (OriginalTextureWrapper.search s f).core)).toInt≤0)','(empty : True)'),
          ('(named : Doom.Proofs.OriginalTextureDash.nameByte (OriginalTextureWrapper.search s f).core≠(0x2d#8))','(named : True)'),
          ('(tableCode : ∀ pc, OriginalTextureTable.program pc≠none → q pc=OriginalTextureTable.program pc)','(tableCode : True)')])
    def test_signed_count_and_read_after_stack_writes(self):
        self.succeeds(HEADER+FIXTURE+'''
example : (OriginalTextureTable.tested (sample 0x80000 0x80000000)).pc=0x3473c ∧
    (OriginalTextureTable.tested (sample 0x80000 0xffffffff)).pc=0x3473c ∧
    (OriginalTextureTable.tested (sample 0x80000 0x7fffffff)).pc=0x3470c := by decide
example : OriginalTextureTable.count (sample 0x300f8 0)=0 ∧
    OriginalTextureTable.count (OriginalTextureDash.prepared (sample 0x300f8 0))=1 := by decide
''')
    def test_first_pointer_read_precedes_call_push_and_frame_requires_separation(self):
        self.succeeds(HEADER+'''
def t : X86Memory.State := ⟨fun r => if r=4 then 0x80000 else if r=7 then 0x61000 else 0,
  store32 (store32 (fun _ => 0) 0x300e0 0x7fffc) 0x7fffc 0x87654321⟩
example : (OriginalTextureTable.comparison t).core.regs 0=0x87654321 ∧
    (OriginalTextureTable.comparison t).core.regs 2=0x61000 ∧
    (OriginalTextureTable.comparison t).core.regs 3=8 ∧
    load32 (OriginalTextureTable.comparison t).core.memory 0x7fffc=0x34722 := by decide
''')
        self.mutations(self.contract('OriginalTextureTable','comparison_frame'),[
          ('(safe : Apart a (s.regs 4-4))','(safe : True)')])
    def test_extraction_rejects_wrong_global_mapping_and_relocations(self):
        e=proof.extraction_support.extraction
        spec=json.loads((ROOT/'tests/reference/original-texture-table.json').read_text());profile=json.loads((ROOT/'tests/reference/original-mul.json').read_text());sw=json.loads((ROOT/'tests/reference/shareware.json').read_text())
        binary=e.original.extract(ROOT/sw['local_directory']/'doom19s.zip',sw,profile)
        for field,value in [('file_offset','0x76715'),('relocations',[]),('hex','90'+spec['units']['table']['hex'][2:])]:
            bad=copy.deepcopy(spec);bad['units']['table'][field]=value
            with self.assertRaises(ValueError):e.extract(binary,profile,bad)
if __name__=='__main__':unittest.main()
